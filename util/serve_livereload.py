#!/usr/bin/env python 
from livereload import Server, shell                                                                                                                                       
server = Server() 
server.watch('./src/*', shell('make lectures')) 
server.watch('./src/course.html', shell('make lectures')) 

for i in range(9):
    server.watch(f'./src/lec{i}/*', shell('make lectures'))
    server.watch(f'./src/psets/pset{i}/*', shell('make lectures'))
    
server.watch('./util/patchup.py', shell('make lectures')) 
server.watch('./media/css/main.css', shell('make media')) 
server.watch('./media/js/*', shell('make media')) 
server.serve(root='../builds/pb701-build/site')

