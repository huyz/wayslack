#!/usr/bin/env python

import os
import re
import sys
import time
import shutil
import urllib
import atexit
import hashlib
import argparse
import codecs
from Queue import Queue
from random import random
from threading import Thread
from itertools import groupby
from datetime import datetime, timedelta

try:
    import ujson as json
except ImportError:
    import json

import json as std_json

import yaml
import pathlib
import requests
from requests.exceptions import HTTPError, ReadTimeout, ConnectionError
from slacker import Slacker, Error
from slacker.utilities import get_api_url

DEBUG = False
VERBOSE = False
JSON_INDENT = None

# In support of the OAuth flow, these are parameters of the "Gimme Slack" app,
# which has been configured with the Redirect URLs:
# - https://huyz.github.io/wayslack/oauth
#   (See GitHub Page https://github.com/huyz/wayslack/blob/gh-pages/oauth.html)
# - http://not.a.realhost/
CLIENT_ID = "2526404912.1280845319991"
CLIENT_SECRET = "76c84535a544d8e70750725feffa6ffb"  # Not really a secret.

ATTR_TO_PACKAGE = {
    'channels': 'conversations',
    'groups': 'conversations',
    'im': 'conversations',
    'mpim': 'conversations',
    'users': 'users',
    'files': 'files',
    'emoji': 'emoji',
}
ATTR_TO_CONVO_TYPE = {
    'channels': 'public_channel',
    'groups': 'private_channel',
    'im': 'im',
    'mpim': 'mpim',
}

BOT_SCOPE = (
    "app_mentions:read,calls:read,channels:history,channels:join,channels:read,dnd:read"
    ",emoji:read,files:read,groups:history,groups:read,im:history,im:read,incoming-webhook"
    ",links:read,mpim:history,mpim:read,pins:read,reactions:read,reminders:read"
    ",remote_files:read,team:read,usergroups:read,users.profile:read,users:read"
    ",users:read.email,files:write"
)
USER_SCOPE = (
    "calls:read,channels:history,channels:read,dnd:read,emoji:read,files:read,groups:history"
    ",groups:read,identify,im:history,im:read,links:read,mpim:history,mpim:read,pins:read"
    ",reactions:read,reminders:read,remote_files:read,search:read,stars:read,team:read"
    ",usergroups:read,users.profile:read,users:read,users:read.email,files:write"
)
REDIRECT_URI_GITHUB = "https://huyz.github.io/wayslack/oauth"
REDIRECT_URI_PARANOID = "http://not.a.realhost/"

def is_slack_url(url):
    return ".slack.com/" in url or "slack-edge.com/" in url or "slack-files.com/" in url

def ts2datetime(ts):
    return datetime.fromtimestamp(ts)

def ts2ymd(ts):
    return ts2datetime(float(ts)).strftime("%Y-%m-%d")

def assert_successful(r):
    if not r.successful:
        raise AssertionError("Request failed: %s" %(r.error, ))

def parse_age_str(s):
    match = re.search("(\d+)\s(m|d)", s)
    if not match:
        return None
    count_str, age_str = match.groups()
    try:
        count = int(count_str)
    except ValueError:
        return None

    multiplier = {"m": 30, "d": 1}.get(age_str)
    if not multiplier:
        return None

    return datetime.now() - timedelta(days=count * multiplier)

def slack_retry(method, *args, **kwargs):
    attempt = 1
    while True:
        try:
            return method(*args, **kwargs)
        except (HTTPError, ConnectionError, ReadTimeout) as e:
            if isinstance(e, ReadTimeout) or isinstance(e, ConnectionError):
                if attempt > 3:
                    raise
                delay = 30
            # As of 2020-08-16, it looks like Slack now temporarily hangs requests rather than returning an error,
            #   probably because it's easier for users to handle this kind of throttling.
            #   This change may have happened then: https://api.slack.com/changelog/2018-03-great-rate-limits
            elif "Too Many Requests" in str(e):
                delay = int(e.response.headers["Retry-After"])
            else:
                raise
            # Note: introduce backoff + random delay so concurrent requests don't spam
            delay = int(delay * (2 ** (attempt * (1 * random()))))
            delay = max(delay, 30)
            if VERBOSE:
                if isinstance(e, ReadTimeout) or isinstance(e, ConnectionError):
                    print "WARNING: Slack aborted or timed out request for %r (retrying in %s seconds)" %(
                        method,
                        delay,
                    )
                elif "Too Many Requests" in str(e):
                    print "WARNING: Slack reported Too Many Requests for %r (retrying in %s seconds)" %(
                        method,
                        delay,
                    )
            time.sleep(delay)
            attempt += 1


# Source: https://github.com/shazow/unstdlib.py/blob/master/unstdlib/standard/string_.py
def to_str(obj, encoding='utf-8', **encode_args):
    r"""
    Returns a ``str`` of ``obj``, encoding using ``encoding`` if necessary. For
    example::
        >>> some_str = b"\xff"
        >>> some_unicode = u"\u1234"
        >>> some_exception = Exception(u'Error: ' + some_unicode)
        >>> r(to_str(some_str))
        b'\xff'
        >>> r(to_str(some_unicode))
        b'\xe1\x88\xb4'
        >>> r(to_str(some_exception))
        b'Error: \xe1\x88\xb4'
        >>> r(to_str([42]))
        b'[42]'
    See source code for detailed semantics.
    """
    # Note: On py3, ``b'x'.__str__()`` returns ``"b'x'"``, so we need to do the
    # explicit check first.
    if isinstance(obj, str):
        return obj

    # We coerce to unicode if '__unicode__' is available because there is no
    # way to specify encoding when calling ``str(obj)``, so, eg,
    # ``str(Exception(u'\u1234'))`` will explode.
    if isinstance(obj, unicode) or hasattr(obj, "__unicode__"):
        # Note: unicode(u'foo') is O(1) (by experimentation)
        return unicode(obj).encode(encoding, **encode_args)

    return str(obj)


# Source: https://github.com/shazow/unstdlib.py/blob/master/unstdlib/standard/contextlib_.py
class open_atomic(object):
    """
    Opens a file for atomic writing by writing to a temporary file, then moving
    the temporary file into place once writing has finished.
    When ``close()`` is called, the temporary file is moved into place,
    overwriting any file which may already exist (except on Windows, see note
    below). If moving the temporary file fails, ``abort()`` will be called *and
    an exception will be raised*.
    If ``abort()`` is called the temporary file will be removed and the
    ``aborted`` attribute will be set to ``True``. No exception will be raised
    if an error is encountered while removing the temporary file; instead, the
    ``abort_error`` attribute will be set to the exception raised by
    ``os.remove`` (note: on Windows, if ``file.close()`` raises an exception,
    ``abort_error`` will be set to that exception; see implementation of
    ``abort()`` for details).
    By default, ``open_atomic`` will put the temporary file in the same
    directory as the target file:
    ``${dirname(target_file)}/.${basename(target_file)}.temp``. See also the
    ``prefix``, ``suffix``, and ``dir`` arguments to ``open_atomic()``. When
    changing these options, remember:
        * The source and the destination must be on the same filesystem,
          otherwise the call to ``os.replace()``/``os.rename()`` may fail (and
          it *will* be much slower than necessary).
        * Using a random temporary name is likely a poor idea, as random names
          will mean it's more likely that temporary files will be left
          abandoned if a process is killed and re-started.
        * The temporary file will be blindly overwritten.
    The ``temp_name`` and ``target_name`` attributes store the temporary
    and target file names, and the ``name`` attribute stores the "current"
    name: if the file is still being written it will store the ``temp_name``,
    and if the temporary file has been moved into place it will store the
    ``target_name``.
    .. note::
        ``open_atomic`` will not work correctly on Windows with Python 2.X or
        Python <= 3.2: the call to ``open_atomic.close()`` will fail when the
        destination file exists (since ``os.rename`` will not overwrite the
        destination file; an exception will be raised and ``abort()`` will be
        called). On Python 3.3 and up ``os.replace`` will be used, which
        will be safe and atomic on both Windows and Unix.
    Example::
        >>> _doctest_setup()
        >>> f = open_atomic("/tmp/open_atomic-example.txt")
        >>> f.temp_name
        '/tmp/.open_atomic-example.txt.temp'
        >>> f.write("Hello, world!") and None
        >>> (os.path.exists(f.target_name), os.path.exists(f.temp_name))
        (False, True)
        >>> f.close()
        >>> os.path.exists("/tmp/open_atomic-example.txt")
        True
    By default, ``open_atomic`` uses the ``open`` builtin, but this behaviour
    can be changed using the ``opener`` argument::
        >>> import io
        >>> f = open_atomic("/tmp/open_atomic-example.txt",
        ...                opener=io.open,
        ...                mode="w+",
        ...                encoding="utf-8")
        >>> some_text = u"\u1234"
        >>> f.write(some_text) and None
        >>> f.seek(0)
        0
        >>> f.read() == some_text
        True
        >>> f.close()
    """

    def __init__(self, name, mode="w", prefix=".", suffix=".temp", dir=None,
                 opener=open, **open_args):
        self.target_name = name
        self.temp_name = self._get_temp_name(name, prefix, suffix, dir)
        self.file = opener(self.temp_name, mode, **open_args)
        self.name = self.temp_name
        self.closed = False
        self.aborted = False
        self.abort_error = None

    def _get_temp_name(self, target, prefix, suffix, dir):
        if dir is None:
            dir = os.path.dirname(target)
        return os.path.join(dir, "%s%s%s" %(
            prefix, os.path.basename(target), suffix,
        ))

    def close(self):
        if self.closed:
            return
        try:
            self.file.close()
            os.rename(self.temp_name, self.target_name)
            self.name = self.target_name
        except:
            try:
                self.abort()
            except:
                pass
            raise
        self.closed = True

    def abort(self):
        try:
            if os.name == "nt":
                # Note: Windows can't remove an open file, so sacrifice some
                # safety and close it before deleting it here. This is only a
                # problem if ``.close()`` raises an exception, which it really
                # shouldn't... But it's probably a better idea to be safe.
                self.file.close()
            os.remove(self.temp_name)
        except OSError as e:
            self.abort_error = e
        self.file.close()
        self.closed = True
        self.aborted = True

    def __enter__(self):
        return self

    def __exit__(self, *exc_info):
        if exc_info[0] is None:
            self.close()
        else:
            self.abort()

    def __getattr__(self, attr):
        return getattr(self.file, attr)

class open_atomic_unicode(open_atomic):
    def __init__(self, name, **kwargs):
        kwargs.update({
            "opener": codecs.open,
            "encoding": "utf-8",
        })
        super(open_atomic_unicode, self).__init__(name, **kwargs)

def pluck(dict, keys):
    return [(k, dict[k]) for k in keys if k in dict]

def sha256(s):
    return hashlib.sha256(s).hexdigest()

def url_to_filename(url, _t_re=re.compile("\?t=[^&]*$")):
    if is_slack_url(url):
        url = _t_re.sub("", url)
    url = urllib.quote(url.encode('utf8'), safe="")
    if len(url) > 190:
        url = url[:50] + "+" + sha256(url) + "+" + url[-50:]
    return url


class Threadpool(object):
    _stop = object()

    def __init__(self, func, thread_count=10, queue_size=1000):
        self._func = func
        self._queue = Queue(maxsize=queue_size)
        self._stop = False
        self._threads = [
            Thread(target=self._run_thread, args=(idx, ))
            for idx in range(thread_count)
        ]
        self._thread_current_item = [
            self._stop for _ in self._threads
        ]
        for t in self._threads:
            t.start()

    def put(self, item):
        self._queue.put(item)

    def qsize(self):
        return self._queue.qsize()

    def stop(self):
        for _ in self._threads:
            self._queue.put(self._stop)

    def join(self):
        self.stop()
        for thread in self._threads:
            thread.join()

    def _run_thread(self, idx):
        # To stop thread when the queue isn't empty?
        while not self._stop:
            try:
                item = self._queue.get()
                if item is self._stop:
                    return
                self._thread_current_item[idx] = item
                self._func(self._thread_current_item[idx])
            finally:
                self._thread_current_item[idx] = self._stop

    def iter_incomplete(self):
        for item in self._thread_current_item:
            if item is not self._stop:
                yield item
        for item in self._queue.queue:
            if item is self._stop:
                continue
            yield item


class Downloader(object):
    def __init__(self, token, path, no_download=False):
        self.counter = 0
        self.token = token
        self.path = path
        if not path.exists():
            self.path.mkdir(parents=True)
        self.lockdir = self.path / "_lockdir"
        if self.lockdir.exists():
            shutil.rmtree(str(self.lockdir))
        self.lockdir.mkdir()
        self.pending_file = self.path / "pending.json"
        self.pool = Threadpool(self._downloader)
        if self.pending_file.exists():
            pending = json.loads(self.pending_file.open().read())
            for item in pending:
                self.pool.put(item)
        atexit.register(self._write_pending)
        self.no_download = no_download

    def _write_pending(self):
        try:
            self.pool.join()
        finally:
            to_write = list(self.pool.iter_incomplete())
            if not to_write:
                try:
                    self.pending_file.unlink()
                except OSError:
                    pass
                return

            with open_atomic_unicode(str(self.pending_file)) as f:
                json.dump(to_write, f, ensure_ascii=False, indent=JSON_INDENT)

    def join(self):
        self.pool.join()

    def _downloader(self, item):
        lockdir = None
        try:
            url, target = item
            if os.path.exists(target):
                return
            base, joiner, name = target.rpartition("/")
            lockdir = self.lockdir / name
            try:
                lockdir.mkdir()
            except OSError:
                lockdir = None
                return

            meta_file = base + joiner + "meta-" + name + ".txt"
            try:
                # Some sites hang and time out if there's no (real?) user-agent
                headers = {
                    "User-Agent": "Mozilla/5.0 (Macintosh; Intel Mac OS X 10_14_6) AppleWebKit/537.36 (KHTML, like Gecko) Chrome/84.0.4147.125 Safari/537.36",
                }
                if is_slack_url(url):
                    headers["Authorization"] = "Bearer %s" %(self.token, )
                res = requests.get(
                    url,
                    headers=headers,
                    stream=True,
                    timeout=60,
                )
            except Exception as e:
                print "ERROR:", e
                with open_atomic(meta_file) as meta:
                    meta.write("999\nException: %r" %(e, ))
                return
            with open_atomic(meta_file) as meta, open_atomic(target) as f:
                meta.write("%s\n%s" %(
                    res.status_code,
                    "\n".join(
                        "%s: %s" %(key, res.headers[key])
                        for key
                        in res.headers
                    ),
                ))
                hash = hashlib.md5()
                for chunk in res.iter_content(4096):
                    hash.update(chunk)
                    f.write(chunk)
                # XXX Slack generally sends an MD5 checksum in the Etag, but they seem to
                #   occasionally version Etags which breaks the checksum somehow.
                if VERBOSE and is_slack_url(url):
                    etag = res.headers.get("etag")
                    if etag:
                        etag = etag.strip('"')
                    if etag and hash.hexdigest() != etag:
                        print("WARNING: Downloading %r: checksum does not match. etag %r != md5 %r\n" %(
                            url,
                            etag,
                            hash.hexdigest(),
                        ))
            self.counter += 1
            print "Downloaded %s (%s left): %s" %(
                self.counter,
                self.pool.qsize(),
                url,
            )
        except:
            if item is not None:
                self.pool.put(item)
            raise
        finally:
            if lockdir is not None:
                lockdir.rmdir()

    def _download_path(self, url):
        return self.path / url_to_filename(url)

    def add(self, urls):
        if self.no_download:
            return
        for _, url in urls:
            download_path = self._download_path(url)
            if not download_path.exists():
                self.pool.put((url, str(download_path)))

    def is_file_missing(self, file_obj):
        download_path = self._download_path(file_obj["url_private"])
        if not download_path.exists():
            return "does not exist", download_path
        size = download_path.stat().st_size
        # Note: Slack appears to compress JPEG files, so ignore this error if
        # the image is a JPEG (the integrity will be checked by the downloader
        # to ensure that the file content is correct, but it may not be
        # identical to the file originally uploaded).
        if size != file_obj["size"] and file_obj["mimetype"] != "image/jpeg":
            msg = "size does not match (actual size %s != expected size %s)" %(
                size,
                file_obj["size"],
            )
            return msg, download_path
        return None, download_path

    def add_file(self, file_obj):
        self.add(pluck(file_obj, [
            "url_private",
            "thumb_480",
        ]))

    def add_message(self, msg):
        for file_obj in msg.get("files") or msg.get("file") or []:
            self.add_file(file_obj)

        for att in msg.get("attachments") or []:
            self.add(pluck(att, [
                "service_icon",
                "thumb_url",
            ]))

    def add_user_profile(self, profile):
        self.add([
            (k, "%s#%s" %(url, profile.get("avatar_hash")))
            for (k, url) in pluck(profile, [
                "image_512",
                "image_192",
                "image_72",
            ])
        ])


class ItemBase(object):
    def __init__(self, attr, slack, downloader, path, obj):
        self.attr = attr
        self.downloader = downloader
        self.slack = slack
        self.__dict__.update(obj)
        self.path = path
        self.pretty_name = (
            "#" + obj["name"] if "name" in obj else
            "im:" + obj["user"]
        )

    @property
    def _is_bot_token(self):
        return self._package.token.startswith("xoxb-")

    @property
    def _package(self):
        return getattr(self.slack, ATTR_TO_PACKAGE[self.attr])

    @staticmethod
    def _is_trunk_message(msg):
        return "thread_ts" not in msg or msg["thread_ts"] == msg["ts"]

    @staticmethod
    def _is_broadcast_message(msg):
        return msg.get("subtype") == "thread_broadcast"

    def refresh(self):
        self._refresh_messages()

    def download_all_files(self):
        for archive in self.iter_archives():
            for msg in self.load_messages(archive):
                if "file" in msg or "files" in msg or "attachments" in msg:
                    self.downloader.add_message(msg)

    def iter_archives(self, reverse=False):
        if not self.path.exists():
            return
        for f in sorted(self.path.glob("*.json"), reverse=reverse):
            yield f

    def load_messages(self, archive):
        with archive.open() as f:
            return json.load(f)

    def _get_list(self, method, latest_ts, **kwargs):
        return slack_retry(method,
            channel=self.id,
            oldest=latest_ts,
            limit=1000,  # Default is 100
            **kwargs
        )

    def _join_channel(self, slack):
        print "Joining channel ", self.pretty_name
        return slack_retry(slack.join, channel=self.id)

    def _leave_channel(self, slack):
        print "Leaving channel ", self.pretty_name
        return slack_retry(slack.leave, channel=self.id)

    def _refresh_messages(self):
        def get_last_saved_replies_ts():
            # type: (...) -> Dict[str, str]
            """
            :returns: a dict mapping parent message's ts -> replies' last successfully saved ts.
            """
            last_saved_replies_ts = dict()
            for archive in self.iter_archives(reverse=True):
                for msg in sorted(self.load_messages(archive), key=lambda m: m["ts"], reverse=True):
                    thread_ts = msg.get("thread_ts")
                    if not self._is_trunk_message(msg) and thread_ts not in last_saved_replies_ts:
                        last_saved_replies_ts[thread_ts] = msg["ts"]
            return last_saved_replies_ts

        def write_fresh_messages(type_str, msgs, latest_ts):
            for day, day_msgs in groupby(msgs, key=lambda m: ts2ymd(m["ts"])):
                day_msgs = list(day_msgs)
                day_archive = self.path / (day + ".json")
                cur = (
                    self.load_messages(day_archive)
                    if day_archive.exists() else []
                )

                # Track new and updated messages, and at the same time eliminate duplicates
                # that may happen to be in the saved files, even though this shouldn't happen.
                cur_msgs = {m["ts"] : m for m in cur}
                new_count = updated_count = 0
                fresh_msgs = []
                for msg in day_msgs:
                    if msg["ts"] in cur_msgs:
                        if std_json.dumps(msg, sort_keys=True) == std_json.dumps(cur_msgs[msg["ts"]], sort_keys=True):
                            continue
                        updated_count += 1
                    else:
                        new_count += 1
                    fresh_msgs.append(msg)
                    cur_msgs[msg["ts"]] = msg
                cur = [cur_msgs[k] for k in sorted(cur_msgs.keys())]

                if new_count > 0:
                    print "%s: %s new %s messages in %s (saving to %s)" %(
                        self.pretty_name, new_count, type_str, self.pretty_name, day_archive,
                    )
                if updated_count > 0:
                    print "%s: %s updated %s messages in %s (saving to %s)" %(
                        self.pretty_name, updated_count, type_str, self.pretty_name, day_archive,
                    )
                for msg in fresh_msgs:
                    if "file" in msg or "files" in msg or "attachments" in msg:
                        self.downloader.add_message(msg)
                with open_atomic_unicode(str(day_archive)) as f:
                    json.dump(cur, f, ensure_ascii=False, indent=JSON_INDENT)
                if len(day_msgs) > 0 and float(day_msgs[-1]["ts"]) > float(latest_ts):
                    latest_ts = day_msgs[-1]["ts"]
            return latest_ts

        slack = self._package

        # For public channels, bot user tokens need to auto-join or otherwise get `not_in_channel`.
        #   For archived channels, this becomes even more complicated as the channel would have to
        #   be unarchived before joining is possible.
        # In contrast, personal oauth tokens don't need to be a member of the public channel to get
        #   messages, even if the channel is archived.  For other reasons, including getting
        #   conversations.replies, you should be using a bot *user* token anyway.
        if self.attr == "channels" and self._is_bot_token and not self.is_member:
            if self.is_archived:
                print "%s: Skipping archived channel because of bot token (try a personal oauth token instead)" %(
                    self.pretty_name
                )
                return
            self._join_channel(slack)

        last_saved_replies_ts = get_last_saved_replies_ts()
        threads_to_fetch = []

        # It's important to start at 1 and not 0.  If you put in 0, the Slack
        # API will give the 1000 latest messages in the first page. But we want
        # the oldest to paginate forward
        latest_ts = 1
        cursor = None
        while True:
            resp = self._get_list(slack.history, latest_ts, cursor=cursor)
            assert_successful(resp)
            cursor = resp.body.get("response_metadata", {}).get("next_cursor")

            # Filter out the broadcast messages that we're already handling among thread replies.
            # (It's important to let the fetch of replies handle these messages as we rely on the
            # continuity to compute get_last_saved_replies_ts)
            msgs = filter(lambda m: not self._is_broadcast_message(m), resp.body["messages"])
            msgs.sort(key=lambda m: m["ts"])

            for msg in msgs:
                if msg["ts"] == msg.get("thread_ts"):
                    if msg["thread_ts"] not in last_saved_replies_ts or \
                            float(msg["latest_reply"]) > float(last_saved_replies_ts[msg["thread_ts"]]):
                        threads_to_fetch.append(msg["ts"])

            if msgs and not self.path.exists():
                self.path.mkdir()

            latest_ts = write_fresh_messages("trunk", msgs, latest_ts)
            if not cursor and not resp.body["has_more"]:
                break

        for thread_ts in threads_to_fetch:
            # It's important to start at 1 and not 0.  If you put in 0, the Slack
            # API will give the 1000 latest messages in the first page. But we want
            # the oldest to paginate forward
            latest_ts = last_saved_replies_ts.get(thread_ts, 1)
            cursor = None
            while True:
                resp = self._get_list(slack.replies, latest_ts, cursor=cursor, ts=thread_ts)
                assert_successful(resp)
                cursor = resp.body.get("response_metadata", {}).get("next_cursor")

                # Filter out the parent messages that we've already added during the fetch of trunk messages.
                # (The first message in a conversations.replies will always be the parent message,
                # no matter what the `oldest` parameter.)
                msgs = filter(lambda m: not self._is_trunk_message(m), resp.body["messages"])
                msgs.sort(key=lambda m: m["ts"])

                if msgs and not self.path.exists():
                    self.path.mkdir()

                latest_ts = write_fresh_messages("reply", msgs, latest_ts)
                if not cursor and not resp.body["has_more"]:
                    break


class BaseArchiver(object):
    name = None
    item_class = ItemBase

    def __init__(self, archive, path):
        self.archive = archive
        self.slack = archive.slack
        self.json_file = path / ("%s.json" %(self.name, ))
        self.path = path

    def get_list(self):
        if not self.json_file.exists():
            return []
        with self.json_file.open() as f:
            return [
                self.item_class(self.attr, self.slack, self.archive.downloader, self.path / o["id"], o)
                for o in json.load(f)
            ]

    @property
    def attr(self):
        return "im" if self.name == "ims" else "mpim" if self.name == "mpims" else self.name

    @property
    def _is_bot_token(self):
        return self._package.token.startswith("xoxb-")

    @property
    def _package(self):
        return getattr(self.slack, ATTR_TO_PACKAGE[self.attr])

    @property
    def _is_convo_type(self):
        return self.attr in ATTR_TO_CONVO_TYPE

    @property
    def _list_args(self):
        return {"types": ATTR_TO_CONVO_TYPE[self.attr]} \
                if self.attr in ATTR_TO_CONVO_TYPE else dict()

    def update(self):
        resp = self._package.list(**self._list_args)
        assert_successful(resp)

        resp_field = (
            "members" if self.name == "users" else
            "channels" if self._is_convo_type else
            self.name
        )
        objs = resp.body[resp_field]
        objs_json = std_json.dumps(objs, sort_keys=True)

        try:
            old_objs_json = self.json_file.open().read()
        except IOError:
            old_objs_json = None
        if objs_json == old_objs_json:
            return

        if not self.path.exists():
            self.path.mkdir()

        ts = datetime.now().isoformat()
        if self.json_file.exists():
            archive_path = self.path / "_json-archive"
            if not archive_path.exists():
                archive_path.mkdir()
            os.rename(
                str(self.json_file),
                str(archive_path / ("%s-%s.json" %(self.name, ts))),
            )

        with open_atomic(str(self.json_file)) as f:
            f.write(unicode(objs_json))

    def upgrade(self):
        return
        yield

    def refresh(self):
        self.update()
        for obj in self.get_list():
            obj.refresh()

    def download_all_files(self):
        for obj in self.get_list():
            obj.download_all_files()


class ArchiveChannels(BaseArchiver):
    name = "channels"

    def upgrade(self):
        archive_channels = self.archive.path / "channels.json"
        if archive_channels.exists() and not archive_channels.is_symlink():
            yield
            if not self.path.exists():
                self.path.mkdir()
            archive_channels.rename(self.json_file)
            archive_channels.symlink_to(os.path.relpath(
                str(self.json_file),
                str(archive_channels.parent),
            ))

        for chandir in self.archive.path.glob("_channel-*"):
            yield
            target = self.path / chandir.name.replace("_channel-", "")
            print "moving %s -> %s" %(chandir, target)
            chandir.rename(target)

        for chan in self.get_list():
            chan_name_dir = self.archive.path / to_str(chan.name)
            if chan_name_dir.is_symlink() or not chan_name_dir.exists():
                continue
            yield
            symlink_target = os.path.relpath(
                str(chan.path),
                str(chan_name_dir.parent),
            )
            print "linking %s -> %s" %(chan_name_dir, symlink_target)
            chan_name_dir.rename(chan.path)
            chan_name_dir.symlink_to(symlink_target)

    def _fixup_symlinks(self):
        for f in self.archive.path.iterdir():
            if not f.is_symlink():
                continue
            if f.exists():
                continue
            target = os.readlink(str(f))
            if "_channels/" in target or "_channel-" in target:
                f.unlink()

        for chan in self.get_list():
            chan_name_dir = self.archive.path / to_str(chan.name)
            if chan_name_dir.exists():
                continue
            symlink_target = os.path.relpath(
                str(chan.path),
                str(chan_name_dir.parent),
            )
            chan_name_dir.symlink_to(symlink_target)

        archive_channels = self.archive.path / "channels.json"
        if not archive_channels.exists():
            if archive_channels.is_symlink():
                archive_channels.unlink()
            archive_channels.symlink_to("_channels/channels.json")

    def refresh(self):
        BaseArchiver.refresh(self)
        self._fixup_symlinks()


class ArchiveGroups(BaseArchiver):
    name = "groups"

    def _fixup_symlinks(self):
        for chan in self.get_list():
            chan_name_dir = self.archive.path / to_str(chan.name)
            if chan_name_dir.exists():
                continue
            if chan_name_dir.is_symlink():
                chan_name_dir.unlink()
            symlink_target = os.path.relpath(
                str(chan.path),
                str(chan_name_dir.parent),
            )
            chan_name_dir.symlink_to(symlink_target)

        archive_channels = self.archive.path / "groups.json"
        if not archive_channels.exists():
            if archive_channels.is_symlink():
                archive_channels.unlink()
            archive_channels.symlink_to("_private/default/_groups/groups.json")

    def refresh(self):
        BaseArchiver.refresh(self)
        self._fixup_symlinks()


class ArchiveMPIMs(BaseArchiver):
    name = "mpims"

    def _fixup_symlinks(self):
        for chan in self.get_list():
            chan_name_dir = self.archive.path / to_str(chan.name)
            if chan_name_dir.exists():
                continue
            if chan_name_dir.is_symlink():
                chan_name_dir.unlink()
            symlink_target = os.path.relpath(
                str(chan.path),
                str(chan_name_dir.parent),
            )
            chan_name_dir.symlink_to(symlink_target)

        archive_channels = self.archive.path / "mpims.json"
        if not archive_channels.exists():
            if archive_channels.is_symlink():
                archive_channels.unlink()
            archive_channels.symlink_to("_private/default/_mpims/mpims.json")

    def refresh(self):
        BaseArchiver.refresh(self)
        self._fixup_symlinks()


class ArchiveIMs(BaseArchiver):
    name = "ims"

    def _fixup_symlinks(self):
        for chan in self.get_list():
            chan_name_dir = self.archive.path / to_str(chan.id)
            if chan_name_dir.exists():
                continue
            if chan_name_dir.is_symlink():
                chan_name_dir.unlink()
            symlink_target = os.path.relpath(
                str(chan.path),
                str(chan_name_dir.parent),
            )
            chan_name_dir.symlink_to(symlink_target)

        archive_channels = self.archive.path / "dms.json"
        if not archive_channels.exists():
            if archive_channels.is_symlink():
                archive_channels.unlink()
            archive_channels.symlink_to("_private/default/_ims/ims.json")

    def refresh(self):
        BaseArchiver.refresh(self)
        self._fixup_symlinks()


class ArchiveUsers(BaseArchiver):
    name = "users"

    def upgrade(self):
        archive_users = self.archive.path / "users.json"
        if archive_users.is_symlink() or not archive_users.exists():
            return
        yield
        if not self.path.exists():
            self.path.mkdir()
        archive_users.rename(self.json_file)
        archive_users.symlink_to(os.path.relpath(
            str(self.json_file),
            str(archive_users.parent),
        ))

    def refresh(self):
        self.update()
        for user in self.get_list():
            self.archive.downloader.add_user_profile(user.profile)
        archive_users = self.archive.path / "users.json"
        if not archive_users.exists():
            archive_users.symlink_to(os.path.relpath(
                str(self.json_file),
                str(self.archive.path),
            ))


class ArchiveFiles(object):
    name = "files"

    def __init__(self, archive, path):
        self.archive = archive
        self.slack = archive.slack
        self.path = path

    def upgrade(self):
        if next(self.path.glob("*http*"), None) is None:
            return
        yield
        storage_dir = self.path / "storage"
        if not storage_dir.exists():
            storage_dir.mkdir()
        for f in self.path.glob("*http*"):
            f.rename(storage_dir / f.name)

    def refresh(self):
        self.status_file = self.path / "status.json"
        self.status = (
            {} if not self.status_file.exists() else
            json.loads(self.status_file.open().read())
        )

        for files in self.iter_file_lists():
            for file_obj in files:
                self.archive.downloader.add_file(file_obj)
                output_dir = self.path / ts2ymd(file_obj["created"])
                if not output_dir.exists():
                    output_dir.mkdir()
                output_file = output_dir / (file_obj["id"] + ".json")
                with open_atomic_unicode(str(output_file)) as f:
                    json.dump(file_obj, f, ensure_ascii=False, indent=JSON_INDENT)

    def update_status(self, x):
        self.status.update(x)
        with open_atomic_unicode(str(self.status_file)) as f:
            json.dump(self.status, f, ensure_ascii=False, indent=JSON_INDENT)

    def iter_file_lists(self):
        """ Iterates over lists of files that need to be saved + downloaded """
        oldest_file = None
        newest_file = self.status.get("newest_file")

        # First, download files older than those we've already retrieved,
        #   in particular, to resume a prior (interrupted) download session.
        # There's no way to list files in reverse order, so instead we need
        #   to start reading files backwards until we hit an empty list, which
        #   means we've hit the oldest file. After that, start reading forward.
        if not self.status.get("oldest_file"):
            print "Walking backwards to find oldest file (this may take a little while)..."

        while not self.status.get("oldest_file"):
            kwargs = {"ts_to": self.status["ts_to_oldest"]} \
                if self.status.get("ts_to_oldest") else {}
            # TODO: we should be using cursor pagination, but slacker/slacker2
            #   don't yet support these arguments
            resp = slack_retry(self.slack.files.list, count=1000, **kwargs)
            assert_successful(resp)
            sorted_files = sorted(resp.body["files"], key=lambda f: f["created"])
            if not sorted_files or sorted_files[0] == oldest_file:
                self.update_status({
                    "oldest_file": oldest_file,
                })
                print "Oldest file found! Starting on new files..."
                break
            yield sorted_files
            oldest_file = sorted_files[0]
            newest_file = sorted_files[-1]
            if oldest_file["created"] > self.status.get("ts_to_oldest", float("inf")):
                raise AssertionError("uh oh %s > %s" %(
                    oldest_file["created"],
                    self.status.get("ts_to_oldest") or 0,
                ))
            self.update_status({
                "ts_to_oldest": oldest_file["created"],
                "ts_from_newest": max(newest_file["created"], self.status.get("ts_from_newest", 0)),
            })

        # Second, download files newer than those we've already retrieved,
        #   since new files may have come in since last time.
        # Now start at the latest file we've seen before and walk forward!
        while True:
            kwargs = {"ts_from": self.status["ts_from_newest"]} \
                if self.status.get("ts_from_newest") else {}
            # TODO: we should be using cursor pagination, but slacker/slacker2
            #   don't yet support these arguments
            resp = slack_retry(self.slack.files.list, count=1000, **kwargs)
            assert_successful(resp)
            sorted_files = sorted(resp.body["files"], key=lambda f: f["created"])
            if not sorted_files or sorted_files[-1] == newest_file:
                self.update_status({
                    "newest_file": newest_file,
                })
                break
            yield sorted_files
            newest_file = sorted_files[-1]
            if newest_file["created"] < self.status.get("ts_from_newest", float("inf")):
                raise AssertionError("uh oh %s > %s" %(
                    oldest_file["created"],
                    self.status.get("ts_to_oldest", 0),
                ))
            self.update_status({
                "ts_from_newest": newest_file["created"],
            })

    def _iter_archive_dirs(self):
        name_re = re.compile("\d{4}-\d{2}-\d{2}")
        for dir in self.path.iterdir():
            if name_re.match(dir.name) and dir.is_dir():
                yield dir

    def _iter_files_in_dir(self, dir):
        for file_file in dir.glob("*.json"):
            with file_file.open() as f:
                yield file_file, json.load(f)

    def download_all_files(self):
        for dir in self._iter_archive_dirs():
            for _, file_obj in self._iter_files_in_dir(dir):
                self.archive.downloader.add_file(file_obj)

    def delete_old_files(self, date, confirm):
        date_str = date.strftime("%Y-%m-%d")
        dry_run = (
            "" if confirm else
            " (PREVIEW ONLY; use '--confirm-delete' to actaully delete these files)"
        )
        print "Deleting files created before %s... %s" %(date_str, dry_run)

        def delete_file(x):
            file_file, file_obj = x
            try:
                res = slack_retry(self.slack.files.delete, file_obj["id"])
                assert_successful(res)
            except Error as e:
                print "ERROR: deleting file %r: %s" %(file_obj["id"], e.message)
                self._error_count += 1
                return
            self._deleted_count += 1
            file_obj["_wayslack_deleted"] = True
            with open_atomic_unicode(str(file_file)) as f:
                json.dump(file_obj, f, ensure_ascii=False, indent=JSON_INDENT)

        pool = Threadpool(delete_file, queue_size=1, thread_count=10)
        self._deleted_count = 0
        self._skipped_count = 0
        self._error_count = 0
        for dir in self.path.iterdir():
            if dir.name >= date_str:
                continue
            for file_file, file_obj in self._iter_files_in_dir(dir):
                if file_obj.get("_wayslack_deleted"):
                    continue
                err, file_path = self.archive.downloader.is_file_missing(file_obj)
                if err:
                    self._skipped_count += 1
                    if VERBOSE:
                        print "WARNING: %s: %s" %(
                            str(file_file),
                            err,
                        )
                        print "         File:", file_path
                        print "          URL:", file_obj["url_private"]
                    continue
                self._deleted_count += 1
                if confirm:
                    if (self._deleted_count + self._error_count + self._skipped_count) % 10 == 0:
                        print self._deleted_msg()
                    pool.put((file_file, file_obj))
        pool.join()
        print "Deleted files: %s%s" %(self._deleted_count, dry_run)
        if self._skipped_count and self._deleted_count:
            print "Skipped files: %s (this is 'normal'. See https://stackoverflow.com/q/44742164/71522; use --verbose for more info)" %(self._skipped_count, )
        if self._error_count:
            print "Errors: %s" %(self._error_count, )

    def _deleted_msg(self):
        msg = "Deleted files: %s" %(self._deleted_count, )
        suffix = []
        if self._error_count:
            suffix.append("errors: %s" %(self._error_count, ))
        if self._skipped_count:
            suffix.append("skipped: %s" %(self._skipped_count, ))
        if suffix:
            msg = "%s (%s)" %(msg, ", ".join(suffix))
        return msg


class EmojiItem(object):
    def __init__(self, slack, downloader, name, url):
        self.downloader = downloader
        self.slack = slack
        self.name = name
        self.url = url

    def refresh(self):
        self.download_all_files()

    def download_all_files(self):
        if self.url.startswith("http"):
            self.downloader.add([(None, self.url)])


class ArchiveEmoji(BaseArchiver):
    name = "emoji"

    def get_list(self):
        if not self.json_file.exists():
            return []
        with self.json_file.open() as f:
            return [
                EmojiItem(self.slack, self.archive.downloader, k, v)
                for (k, v) in json.load(f).iteritems()
            ]


class SlackArchive(object):
    def __init__(self, slack, opts):
        self.opts = opts
        self.dir = opts["dir"]
        self.download_files = opts.get("download_files", True)
        self.slack = slack
        self.path = pathlib.Path(self.dir)
        self.emoji = ArchiveEmoji(self, self.path / "_emoji")
        self.files = ArchiveFiles(self, self.path / "_files")
        self.users = ArchiveUsers(self, self.path / "_users")
        self.channels = ArchiveChannels(self, self.path / "_channels")
        private_dir = self.path / "_private" / "default"
        if not private_dir.exists():
            os.makedirs(str(private_dir))
        self.groups = ArchiveGroups(self, private_dir / "_groups")
        self.mpims = ArchiveMPIMs(self, private_dir / "_mpims")
        self.ims = ArchiveIMs(self, private_dir / "_ims")
        self.subtypes = [
            self.emoji,
            self.files,
            self.users,
            self.channels,
            self.groups,
            self.mpims,
            self.ims,
        ]
        if not opts.get("download_public_data", True):
            self.subtypes.remove(self.files)
            self.subtypes.remove(self.channels)

    def __enter__(self):
        self.downloader = Downloader(
            self.slack.api.token,
            self.path / "_files" / "storage",
            no_download=not self.download_files,
        )
        return self

    def __exit__(self, *a):
        self.downloader.join()

    def _upgrade(self):
        if not self.path.exists():
            yield
            self.path.mkdir()

        for sub in self.subtypes:
            for _ in sub.upgrade():
                yield

    def needs_upgrade(self):
        for _ in self._upgrade():
            return True
        return False

    def upgrade(self):
        for _ in self._upgrade():
            pass

    def download_all_files(self):
        for sub in self.subtypes:
            sub.download_all_files()

    def refresh(self):
        for sub in self.subtypes:
            print "%s..." %(sub.name, )
            sub.refresh()

    def delete_old_files(self, confirm=False):
        age_str = self.opts.get("delete_old_files")
        if not age_str:
            return
        age = parse_age_str(age_str)
        if not age:
            raise AssertionError("Invalid age for delete_old_files: %r" %(age_str, ))
        self.files.delete_old_files(age, confirm)


def args_get_archives(args):
    config_archives = []
    default_config_file = os.path.expanduser("~/.wayslack/config.yaml")
    config_file = (
        args.config if args.config else
        default_config_file if os.path.exists(default_config_file) else
        None
    )
    if config_file:
        config = yaml.load(open(config_file))
        for archive in config["archives"]:
            archive.setdefault("name", archive["dir"])
            archive["dir"] = os.path.expanduser(archive["dir"])
            archive["dir"] = os.path.join(os.path.dirname(config_file), archive["dir"])
            config_archives.append(archive)

    if not args.archive:
        for ca in config_archives:
            yield ca
        return

    for a in args.archive:
        token, _, path = a.rpartition(":")
        path = os.path.expanduser(path)
        for ca in config_archives:
            if ca["dir"].rstrip("/") == path.rstrip("/"):
                yield ca
                break
        else:
            if not os.path.isdir(path):
                print "Note: directory will be created: %s" %(path, )
            while not token:
                token = raw_input("API token for %s (See https://api.slack.com/authentication/token-types#user): " %(path, ))
            yield {
                "token": token,
                "dir": path,
                "name": path,
            }

# Based on https://github.com/wee-slack/wee-slack/blob/c561fb7de35175fa5db58aef3ce227ba3cf9eedb/wee_slack.py#L4260-L4314
def register_app(args):
    def request_secrets():
        result = exchange_for_oauth_token()
        return save_secrets(result) if result else 1

    def exchange_for_oauth_token():
        # TODO: use slacker/slacker2 once they support oauth.v2.access
        resp = requests.post(get_api_url("oauth.v2.access"), {
            "client_id": CLIENT_ID,
            "client_secret": CLIENT_SECRET,
            "redirect_uri": redirect_uri,
            "code": code,
        })
        if not resp.ok:
            print "ERROR: problem when trying to get Slack OAuth token. Got return code {}".format(
                resp.status_code
            )
            print "  Check the network or proxy settings"
            return
        body = resp.json()
        if not body["ok"]:
            print "ERROR: Couldn't get Slack OAuth token: {}".format(body["error"])
            return

        workspace = body["team"]["name"]
        token = body["authed_user"]["access_token"]
        result = {
            "workspace": workspace,
            "token": token,
        }
        if "incoming_webhook" in body:
            webhook_channel = body["incoming_webhook"].get("channel")
            webhook_url = body["incoming_webhook"].get("url")
            webhook_note = "Your webhook URL for channel {} is:\n{}".format(
                webhook_channel,
                webhook_url,
            )
            result.update({
                "webhook_channel": webhook_channel,
                "webhook_url": webhook_url,
            })
        else:
            webhook_note = ""

        print """
### Successfully registered "Gimme Slack" into the "{}" workspace ###

Your personal OAuth token is:
{}
{}
""".format(workspace, token, webhook_note)
        return result

    def save_secrets(secrets):
        output = """\
    # Token for the "{0}" workspace
    token: {1}\
""".format(secrets["workspace"], secrets["token"])
        if secrets.get("webhook_url"):
            output += """
    # Webhook URL for the "{0} {1}" channel
    webhook_url: {2}\
""".format(secrets["workspace"], secrets["webhook_channel"], secrets["webhook_url"])
        output = DEFAULT_CONFIG_FILE.format(output)

        default_config_file = os.path.expanduser("~/.wayslack/config.yaml")
        fallback_default_config_file = os.path.expanduser("~/.wayslack/config.default.yaml")
        config_file = (
            args.config if args.config and not os.path.exists(args.config) else
            default_config_file if not os.path.exists(default_config_file) else
            fallback_default_config_file
        )

        if not os.path.exists(os.path.dirname(config_file)):
            os.makedirs(os.path.dirname(config_file))
        try:
            with open_atomic(config_file) as f:
                f.write(output)
            print "Saved secrets in the config file {}".format(config_file)
            return
        except IOError, e:
            print "ERROR: can't write the config file {}: {}".format(config_file, e)
            return 1

    paranoid = args.paranoid
    redirect_uri = REDIRECT_URI_PARANOID if paranoid else REDIRECT_URI_GITHUB
    redirect_uri_quoted = urllib.quote(redirect_uri, safe='')
    code = args.archive

    if code:
        return request_secrets()

    if paranoid:
        paranoid_note = ""
        last_step = ("""\
You will see a message that the site can't be reached--this is expected.
   The URL for the page will have a code in it of the form `?code=CODE`. Copy
   the code after the equals sign (but excluding any `&state=`, if any),
   return to your terminal and run `wayslack --register --paranoid CODE`.
""")
    else:
        paranoid_note = ("""
Note that by default GitHub Pages could theoretically grab the temporary code
used to create your token (but not the long-lived token itself). If you're
worried about this very low risk, you can use the --paranoid option, although
the process would be a bit less user-friendly.\
""")
        last_step = ("""\
The web page will show a command in the form `wayslack --register CODE`.
   Run this command in your terminal.
""")
    print """
### Registering the "Gimme Slack" app with your Slack workspace using OAuth ###
{}

1) Paste this link into a browser:

   https://slack.com/oauth/v2/authorize?client_id={}&scope={}&user_scope={}&redirect_uri={}
   
2) In your browser, select the workspace you wish Wayslack to access. If you
   want to register with multiple workspaces or multiple users in the same
   workspace, you will have to repeat this whole process to get a new token
   (and webhook URL) each time.
3) Click "Authorize" in the browser.
   If you get a message saying you are not authorized to install "Gimme Slack",
   the workspace admins have restricted Slack app installation and you will
   have to request permission from an admin.
   To do that, go to https://my.slack.com/apps/A0188QV9DV5-gimme-slack and
   click "Request to Install".
4) {}
""".format(paranoid_note, CLIENT_ID, BOT_SCOPE, USER_SCOPE, redirect_uri_quoted, last_step)

def main(argv=None):
    global VERBOSE, DEBUG, JSON_INDENT
    argv = sys.argv[1:] if argv is None else argv
    args = parser.parse_args(argv)
    VERBOSE = args.verbose
    DEBUG = args.debug

    if DEBUG:
        VERBOSE = True
        JSON_INDENT = 4  # Default is None
        import logging
        logging.basicConfig(level=logging.DEBUG)

    if args.register:
        return register_app(args)

    archives = list(args_get_archives(args))
    if not archives:
        print "ERROR: no archives specified. Specify an archive or a config file."
        return 1

    for a in archives:
        print "Processing:", a["name"]
        slack = Slacker(a["token"])
        with SlackArchive(slack, a) as archive:
            needs_upgrade = archive.needs_upgrade()
            if needs_upgrade:
                print "Notice: wayslack needs to fiddle around with some symlinks."
                print "This will cause some non-destructive changes to the directory."
                res = raw_input("Continue? Y/n: ")
                if res and res.lower()[:1] != "y":
                    break
                archive.upgrade()

            if needs_upgrade or args.download_everything:
                archive.download_all_files()

            archive.refresh()
        archive.delete_old_files(args.confirm_delete)


DEFAULT_CONFIG_FILE = """\
archives:
  - dir: ~/wayslack-export  # path is relative to this file
{}
    # Delete files from Slack if they're more than 60 days old (useful for
    #   free Slack channels which have a file limit).
    # Files will only be deleted from Slack if:
    #   - They exist in the archive (_files/storage/...)
    #   - wayslack is run with --confirm-delete
    # Otherwise a message will be printed but files will not be deleted.
    #delete_old_files: 60 days
    # Do not download any files; only download conversation text.
    #download_files: false
    # Only download private conversations and files
    #download_public_data: false
"""

example_config_file = """---
archives:
  - dir: path/to/public-export # path is relative to this file
    # Get token (and webhook URL) by either:
    #   a) running `wayslack --register`
    #   b) creating an app and installing it to your workspace at https://api.slack.com/apps
    token: xoxp-1234-abcd
    #webhook_url: https://hooks.slack.com/services/...
    # Delete files from Slack if they're more than 60 days old (useful for
    #   free Slack channels which have a file limit).
    # Files will only be deleted from Slack if:
    #   - They exist in the archive (_files/storage/...)
    #   - wayslack is run with --confirm-delete
    # Otherwise a message will be printed but files will not be deleted.
    delete_old_files: 60 days
  - dir: private-export
    token: xoxp-9876-wxyz
    #webhook_url: https://hooks.slack.com/services/...
    # Do not download any files; only download conversation text.
    download_files: false
    # Only download private conversations and files
    download_public_data: false
"""

parser = argparse.ArgumentParser(formatter_class=argparse.RawTextHelpFormatter, description="""
Incrementally archive all content from a Slack team using the Slack export
format.

To get started:

1. (optional) Export your team history:
   https://slack.com/help/articles/201658943-Export-your-workspace-data

2. Either,

    a) Run `wayslack --register` to go through an automated workflow

        1) This automatically creates a default `~/.wayslack/config.yaml` file
           with your "OAuth Access Token" and "Webhook URL"
        2) Customize `~/.wayslack/config.yaml` (See below).

    or

    b) Get a token by creating an app: https://api.slack.com/apps

        1) (optional) Bot token scopes: give the `incoming-webhook` if you want
           to receive a notification for completed operations
        2) User token scopes: give the app all the `*:read`, `*:history`,
           `identify` scopes
        3) (optional) User token scopes: give the `files:write` scope if you
           want wayslack to be able to delete old files
        4) Retrieve the "OAuth Access Token" on the "OAuth & Permissions" page.
           Don't confuse that with the (limited) "Bot User OAuth Access Token".
        5) (optional) Retrieve the "Webhook URL" on the "Incoming Webhooks" page

3. Run `wayslack path/to/export/directory` and enter the token when prompted

Optionally, create a configuration file:

$ cat ~/.wayslack/config.yaml
%s
""" %(example_config_file, ))
parser.add_argument("--config", "-c", help="Configuration file. Default: ~/.wayslack/config.yaml")
parser.add_argument("--debug", action="store_true", help="""
    Turn on noisy debugging logs, especially network calls, and pretty-print
    the JSON files that are exported.
    This automatically sets the verbose flag.
""")
parser.add_argument("--verbose", "-v", action="store_true")
parser.add_argument("--download-everything", "-d", default=False, action="store_true", help="""
    Re-scan all messages for files to download (by default only new files are
    downloaded, except on the first run when all files are downloaded). This
    option generally isn't necessary.
""")
parser.add_argument("--confirm-delete", "-D", default=False, action="store_true", help="""
    Confirm that Wayslack should delete old files from slack (see the
    delete_old_files configuration option).
""")
parser.add_argument("--register", action="store_true", help="""
    Go through an OAuth workflow to register the app with your workspace and
    obtain a token so that Wayslack can have the read permissions of your user
    and the write permissions to send notifications.
""")
parser.add_argument("--paranoid", action="store_true", help="""
    When you do --register, GitHub Pages will see a temporary code used to
    create your token (but not the token itself). If you're worried about this,
    you can use the --paranoid option, though the process will be a bit less
    user-friendly.
""")
parser.add_argument("archive", nargs="*", default=[], help="""
    Path to a Slack export directory. A token can be provided by prefixing
    the path with the token: "token:path" (for example,
    "xoxp-1234-abcd:~/Downloads/foo"). Get a token by creating an
    app and installing it to your workspace at https://api.slack.com/apps .
""")

if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
