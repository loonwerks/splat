#!/usr/bin/env python3

'''
Created on May 16, 2019

'''

import os
import re
import sys

from github3 import GitHub
from pprint import pformat

GITHUB_API = 'https://api.github.com/repos'
GITHUB_RELEASES = 'releases'
AUTH_TOKEN = os.environ['GH_TOKEN'] if 'GH_TOKEN' in os.environ.keys() else None

REPOSITORY_OWNER = 'loonwerks'
REPOSITORY_REPO = 'splat'

def manage_builds(sname):
    print('Managing builds matching %s' % (sname))
    # obtain git handle
    gh = GitHub(GITHUB_API, token=AUTH_TOKEN)
    repository = gh.repository(REPOSITORY_OWNER, REPOSITORY_REPO)
    # get list of releases
    releases = repository.releases()
    # extract keys and sort by build date
    release_keys = {x.id : x.created_at for x in releases if sname in x.name} 
    sorted_keys = sorted(release_keys.items(), reverse=True, key=lambda x: x[1])
    print('%s' % (pformat(sorted_keys)))
    # filter to obtain the keys to delete
    delete_keys = [v[0] for v in sorted_keys[2:]]
    print('Deleting releases: %s' % (pformat(delete_keys)))
    # iterate, deleting the releases and corresponding tags
    for rel in releases:
        print('examining rel %d from %s...' % (rel.id, str(rel.created_at)))
        if rel.id in delete_keys and rel.tag_name is not None:
            print(' deleting release id %d and tag %s.' % (rel.id, rel.tag_name))
            rel_tag_ref = repository.ref('tags/%s' % (rel.tag_name))
            rel.delete()
            if rel_tag_ref is not None:
                print('  deleting tag %s' % (rel_tag_ref.ref))
                rel_tag_ref.delete()

if __name__ == '__main__':
    manage_builds(sys.argv[1])
