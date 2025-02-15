#!/usr/bin/env python 
from livereload import Server, shell                                                                                                                                       
server = Server() 
server.watch('./src/*', shell('make lectures')) 
server.watch('./src/psets/*', shell('make lectures')) 
server.watch('./src/psets/pset1', shell('make lectures')) 
server.watch('./src/psets/pset2/*', shell('make lectures')) 
server.watch('./util/patchup.py', shell('make lectures')) 
server.watch('./media/css/main.css', shell('make media')) 
server.watch('./media/js/*', shell('make media')) 
server.serve(root='../builds/pb701-build/site')

