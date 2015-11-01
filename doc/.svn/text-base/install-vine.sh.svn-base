#!/bin/bash
# Instructions for installing VinE on Linux

# In the form of a shell script that runs on a fresh Ubuntu 8.04
# installation. Some adaptation may be needed for other systems.
# Things that require root access are preceded with "sudo".

# See the "INSTALL" file in the VinE source for more discussion on
# what we're doing here.

# Last tested 2008-09-11

# This script will build VinE in a "$HOME/bitblaze" directory
cd ~
mkdir bitblaze
cd bitblaze

# Prerequisite: Valgrind VEX r1749
# VinE uses the VEX library that comes with Valgrind to interpret the
# semantics of instructions. (Note we don't even bother to compile
# Valgrind itself). Because of changes in the VEX interface, earlier
# or later revisions will probably not work without some changes,
# though we'll probably update to work with a more recent version at
# some point in the future.

# Packages needed to build Valgrind:
sudo apt-get build-dep valgrind
# Extra packages needed to build the SVN version:
sudo apt-get install subversion automake
svn co -r6697 svn://svn.valgrind.org/valgrind/trunk valgrind
(cd valgrind/VEX && svn up -r1749)
(cd valgrind/VEX && make version && make libvex_x86_linux.a && make libvex.a)

# Other prerequisite packages:

# For C++ support:
sudo apt-get install g++

# For OCaml support:
sudo apt-get install ocaml ocaml-findlib libgdome2-ocaml-dev camlidl \
                     libextlib-ocaml-dev

# For the BFD library:
sudo apt-get install binutils-dev

# For the Boost Graph library:
sudo apt-get install libboost-dev libboost-graph-dev

# For the SQLite database:
sudo apt-get install libsqlite3-dev sqlite3 libsqlite3-0 libsqlite3-ocaml-dev

# For building documentation:
sudo apt-get install texlive

# Ocamlgraph >= 0.99c is required. Ocamlgraph is packaged by Debian
# and Ubuntu as libocamlgraph-ocaml-dev, but the latest version in
# Ubuntu is 0.98. The following process for building a package from
# the Debian repository is a bit of a hack.
sudo apt-get install   libocamlgraph-ocaml-dev
sudo apt-get build-dep libocamlgraph-ocaml-dev
sudo apt-get install liblablgtk2-ocaml-dev liblablgtk2-gnome-ocaml-dev \
                     docbook-xsl po4a
sudo apt-get install fakeroot
svn co svn://svn.debian.org/svn/pkg-ocaml-maint/trunk/packages/ocamlgraph \
       -r5983
tar xvzf ocamlgraph/upstream/ocamlgraph_0.99c.orig.tar.gz
mv ocamlgraph/trunk/debian ocamlgraph-0.99c
perl -pi -e 's[ocaml-nox \(>= 3.10.0-9\)] #\
              [ocaml-nox  (>= 3.10.0-8)]' ocamlgraph-0.99c/debian/control
(cd ocamlgraph-0.99c && dpkg-buildpackage -us -uc -rfakeroot)
sudo dpkg -i libocamlgraph-ocaml-dev_0.99c-2_i386.deb

# VinE itself:
# Trunk:
svn co https://bullseye.cs.berkeley.edu/svn/vine/trunk vine
(cd vine && ./autogen.sh)
(cd vine && ./configure --with-vex=$HOME/bitblaze/valgrind/VEX)
(cd vine && make)
(cd vine/doc && make doc)
