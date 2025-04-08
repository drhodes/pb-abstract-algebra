#!/usr/bin/env python
import os
import re
from livereload import Server
import logging
import shlex
from subprocess import Popen, PIPE

CSS_FILE="../builds/pb701-build/site/media/css/main.css"
logger = logging.getLogger('livereload')

def update_color_of_css():
    # Define the string to append
    new_css = "body {\n  background-color: red;\n}\n"

    # Append the string to the end of the CSS file
    with open(CSS_FILE, 'a') as file:
        file.write(new_css)

    print("CSS for body background-color updated to red.")

'''
 this shell command reused from internal python-livereload

    :copyright: (c) 2013 - 2015 by Hsiaoming Yang
    :license: BSD, see LICENSE for more details.
'''
def shell(cmd, output=None, mode='w', cwd=None, shell=False):
    """Execute a shell command.

    You can add a shell command::

        server.watch(
            'style.less', shell('lessc style.less', output='style.css')
        )

    :param cmd: a shell command, string or list
    :param output: output stdout to the given file
    :param mode: only works with output, mode ``w`` means write,
                 mode ``a`` means append
    :param cwd: set working directory before command is executed.
    :param shell: if true, on Unix the executable argument specifies a
                  replacement shell for the default ``/bin/sh``.
    """
    if not output:
        output = os.devnull
    else:
        folder = os.path.dirname(output)
        if folder and not os.path.isdir(folder):
            os.makedirs(folder)

    if not isinstance(cmd, (list, tuple)) and not shell:
        cmd = shlex.split(cmd)

    def run_shell():
        try:
            p = Popen(cmd, stdin=PIPE, stdout=PIPE, stderr=PIPE, cwd=cwd, shell=shell)
        except OSError as e:
            logger.error(e)
            if e.errno == errno.ENOENT:  # file (command) not found
                logger.error("maybe you haven't installed %s", cmd[0])
            return e
        stdout, stderr = p.communicate()
        #: stdout is bytes, decode for python3
        stdout = stdout.decode()
        stderr = stderr.decode()
        if stderr:
            update_color_of_css() # added this line.
            logger.error(stderr)
            return stderr
        with open(output, mode) as f:
            f.write(stdout)

    return run_shell


server = Server() 
server.watch('./src/*', shell('make lectures')) 
server.watch('./src/course.html', shell('make lectures')) 
server.watch('./src/pb701/Pb701/*', shell('make lectures'))

for i in range(10):
    server.watch(f'./src/lec{i}/*', shell('make lectures'))
    server.watch(f'./src/psets/pset{i}/*', shell('make lectures'))

    
server.watch('./util/patchup.py', shell('make lectures')) 
server.watch('./media/css/main.css', shell('make media')) 
server.watch('./media/js/*', shell('make media')) 
server.serve(root='../builds/pb701-build/site')


