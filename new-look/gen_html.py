#!/usr/bin/env python

import argparse


# Read arguments

parser = argparse.ArgumentParser(description='generates html files from html.part files using a template')
parser.add_argument('filenames', metavar='N', type=str, nargs='+',
                   help='filenames to be processed')
parser.add_argument('--template', metavar='names', type=str, nargs='?',
                   default='template.html',
                   help='file name for template html file')

args = parser.parse_args()

# Run HOL

template = ''.join(open(args.template,'r').readlines())

for filename in args.filenames:
  if (filename.endswith('.part')):
    f = open(filename,'r')
    all_lines = f.readlines()
    f.close()
    title = all_lines.pop(0)      # first line
    long_title = all_lines.pop(0) # second line
    content = ''.join(all_lines) # the rest
    new_filename = filename[:-5]
    url = 'http://hol-theorem-prover.org/new-look/' + new_filename
    str = template.replace('[TITLE]',title)
    str = str.replace('[LONG_TITLE]',long_title)
    str = str.replace('[URL]',url)
    str = str.replace('[CONTENT]',content)
    f = open(new_filename,'w')
    f.write(str)
    f.close()
    print('Wrote ' + new_filename + '\n  title: ' + title.strip() + '\n  long title: ' + long_title.strip())
  else:
    print('WARNING: Ignoring ' + filename + " because it doesn't end in .part")
