#!/bin/bash

################################################################################
#
# Builds and installs CIVL in BASE_DIR (see shell var below in settings).
#
################################################################################

# Exit on error
set -e

################################################################################

# Settings

# Change this to the desired path (default uses working-dir/civl-project)
BASE_DIR=`pwd`/civl-project

# Set these flags to control various installation options
INSTALL_PACKAGES=1
INSTALL_CVC3=1
INSTALL_CIVL=1

# Other dirs
CVC3_DIR="${BASE_DIR}/cvc3"
CIVL_DIR="${BASE_DIR}/civl"

################################################################################

# Install required packages

if [ ${INSTALL_PACKAGES} -eq 1 ]; then

sudo apt-get install flex --assume-yes
sudo apt-get install bison --assume-yes
sudo apt-get install libgmp10 --assume-yes
sudo apt-get install libgmp-dev --assume-yes
sudo apt-get install openjdk-7-jdk --assume-yes

fi

################################################################################

# Set up directories

# Base directory for everything
mkdir -p ${BASE_DIR}

# Other dirs
mkdir -p ${CVC3_DIR}
mkdir -p ${CIVL_DIR}

cd ${BASE_DIR}

################################################################################

# CVC3

if [ ${INSTALL_CVC3} -eq 1 ]; then

# Get CVC3
wget http://www.cs.nyu.edu/acsys/cvc3/releases/2.4.1/cvc3-2.4.1.tar.gz
tar -C ${CVC3_DIR} -xzvf cvc3-2.4.1.tar.gz --strip 1

cd ${CVC3_DIR}
./configure CXXFLAGS=-m32 --enable-dynamic --enable-java --with-java-home=/usr/lib/jvm/java-7-openjdk-i386

cd ${BASE_DIR}

fi

################################################################################

# CIVL

if [ ${INSTALL_CIVL} -eq 1 ]; then

# Get CIVL
wget http://vsl.cis.udel.edu/civl/test/trunk/latest/release/CIVL-linux32-trunk_128.tgz
tar -C ${CIVL_DIR} -xzvf CIVL-linux32-trunk_128.tgz --strip 2

export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:${CVC3_DIR}/java/lib
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:${CVC3_DIR}/java/lib/i686-linux-gnu
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:${CVC3_DIR}/lib
export LD_LIBRARY_PATH=$LD_LIBRARY_PATH:${CVC3_DIR}/lib/i686-linux-gnu

export PATH=$PATH:${CIVL_DIR}/bin

cd ${CIVL_DIR}/examples
civl barrier.cvl

cd ${BASE_DIR}

fi

################################################################################

