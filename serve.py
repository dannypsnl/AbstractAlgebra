from livereload import Server, shell
server = Server()
server.watch('src/**/*.md', shell('make'))
server.watch('html/*.html', shell('make'))
server.watch('content/**/*.scrbl', shell('make'))
server.serve(root='_build', port=5321)
