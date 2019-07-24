FROM coqorg/coq
# We start with Coq from the official source.

RUN git clone https://github.com/anshumanmohan/RamifyCoq_VST
# We download our project from Github.

RUN sudo apt-get update && sudo apt-get install -y emacs25
# Next, to help readers explore our code, we add a text editor.

RUN git clone https://github.com/ProofGeneral/PG ~/.emacs.d/lisp/PG && cd ~/.emacs.d/lisp/PG && make && echo "(load \"~/.emacs.d/lisp/PG/generic/proof-site\")" >> ~/.emacs.d/init.el
# Finally, we download ProofGeneral and add it to the Emacs init file.
# This gives additional syntax highlighting, a REPL, etc.

# NOTE:
# All the RUN commands above will execute when "docker build" is run.
# The final CMD command below will execute when "docker run" is run. The latter is very slow.
# Users may want to go to Docker Preferences > Advanced
#   and dedicate a large amount of RAM and CPU storage to the Docker machine
#   to speed up the build. We tested with 4 CPUs, 8GB memory, and 4GB swap.
# This will also prevent processes from being killed by the Docker daemon
#   for overusing resources.

CMD cd RamifyCoq_VST/RamifyCoq/ && make vstandme7
# For technical reasons, we employ the CMD field to build our project.
# The alternate approach, i.e. to run the make command as a RUN command,
#   was giving us trouble.
# This means that users must first build this dockerfile with some tag:
#   docker build -t imagename .
# And finally run the build *without a command*, i.e.:
#   docker run -it imagename
# The imagename is, of course, just a variable.
# Please note the period in the build step.

# After the build completes, control will simply return to the host machine with no comment.
# Please run "docker ps -a" to find the name of the container that was last closed.
#   For example, ours was called "inspiring_mayer"
# Then run, for example: sudo docker commit inspiring_mayer imagename
# This commits all the work from "make vstandme7" to the image.
# Then you can open up your image with: docker run -it imagename bash

# If this is all too cumbersome and slow, we encourage users to use our
#   fully compiled build available via: docker pull johndoe2019/ramifycoq
# That repository is simply this very Dockerfile, but in that case we
#   (1) opened up the image
#   (2) compiled it using "make vstandme7" as shown here
#   (3) committed the changes to the image
#   (4) pushed that image to the repository
# This allows users to avoid compiling the code themselves.
# The run command would then be:
#   docker run -it johndoe2019/ramifycoq bash
# thus giving them a bash CLI to start with.