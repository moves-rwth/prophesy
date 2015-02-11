# Add non-default repositories
#sudo add-apt-repository ppa:jkeiren/ppa -y #libboost1.49
# sudo add-apt-repository ppa:apokluda/boost1.57 -y #libboost1.53
#sudo add-apt-repository ppa:ubuntu-toolchain-r/test -y #gcc-4.8, g++-4.8
sudo apt-get update

# Install sympy, it is not in the repositories
sudo pip3 install sympy

# Install vbox guest additions
sudo mount -oloop /usr/share/virtualbox/VBoxGuestAdditions.iso /mnt
sudo sh /mnt/VBoxLinuxAdditions.run
sudo umount /mnt

# Enable auto-login
cat << EOF | sudo tee -a /etc/lightdm/lightdm.conf

[SeatDefaults]
autologin-user=prophesy
autologin-user-timeout=0

EOF

# Make locations to put tools in
mkdir /home/prophesy/bin
mkdir /home/prophesy/lib

# Fetch tools, and put them in the right location
#TODO wget
tar -xaf tools.tar.gz ./

# Fetch prophesy
#TODO wget
tar -xaf prophesy.tar.gz ./

# Make prism work
cd /home/prophesy/bin/prism-4.2.1-linux
./install.sh
cp bin/prism ../
cd

# Make sure libraries can be found
sudo sh -c "echo /home/prophesy/lib > /etc/ld.so.conf.d/prophesy.conf"
sudo ldconfig

# Put icon on the desktop to start the webserver
chmod a+x "Prophesy Server.desktop"
# Put icon on the desktop pointing to locahost:4242
chmod a+x "Prophesy GUI.desktop"