# Add non-default repositories
#sudo add-apt-repository ppa:jkeiren/ppa -y #libboost1.49
# sudo add-apt-repository ppa:apokluda/boost1.57 -y #libboost1.53
#sudo add-apt-repository ppa:ubuntu-toolchain-r/test -y #gcc-4.8, g++-4.8
sudo apt-get update

# Build metapackage
sudo equivs-build prophesy-metaconfig
# Install metapackage
sudo gdebi prophesy-metapackage_1.0_all.deb

# Checkout 
rm -r benchmark-files
mkdir benchmark-files
# rm -r hasdel-devel
# mkdir hasdel-devel
# clear
# git config --global http.sslverify false
# git clone https://srv-i2.informatik.rwth-aachen.de:8443/git/hasdel_devel.git hasdel-devel
# cd hasdel-devel
# git checkout hasdel
# 
# cd tools
# # Build SLIM parser and IMCA
# make clean
# make distclean
# make build
# make build
# make imca
# 
# # Build dft2mrmc and sigref2mrmc
# cd mrmc_conv
# cmake CMakeLists.txt
# make
# cp bin/* ../bin/
