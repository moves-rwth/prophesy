cd

sudo chown -R prophesy:prophesy Desktop

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

# Fetch tools
wget http://moves.rwth-aachen.de/wp-content/uploads/prophesy/tools.zip
unzip tools.zip

# Fetch prophesy
wget http://moves.rwth-aachen.de/wp-content/uploads/prophesy/prophesy.zip
unzip prophesy.zip

# Fetch examples
wget http://moves.rwth-aachen.de/wp-content/uploads/prophesy/examples.zip
unzip examples.zip

# Make prism work
cd /home/prophesy/bin/prism-4.2.1-linux
./install.sh
cp bin/prism ../
cd

# Make sure libraries can be found
sudo touch /etc/ld.so.conf.d/prophesy.conf
echo /home/prophesy/lib | sudo tee -a /etc/ld.so.conf.d/prophesy.conf
sudo ldconfig

# Put icon on the desktop to start the webserver
chmod a+x "Desktop/Prophesy Server.desktop"
# Put icon on the desktop pointing to locahost:4242
chmod a+x "Desktop/Prophesy GUI.desktop"

history -c && history -w
