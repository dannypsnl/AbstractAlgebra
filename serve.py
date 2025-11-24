from livereload import Server, shell
server = Server()
server.watch('src/**/*.md', shell('make'))
server.watch('html/*.html', shell('raco tr build'))
server.watch('content/**/*.scrbl', shell('raco tr build'))
server.serve(root='_build', port=5321)
