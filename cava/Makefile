#
# Copyright 2019 The Project Oak Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

.PHONY: all clean

all:
	cd arrow-lib && $(MAKE)
	cd cava && $(MAKE)
	cd monad-examples && $(MAKE)
	cd monad-examples/xilinx && $(MAKE) extraction
	cd tests/xilinx && $(MAKE) extraction
	cd arrow-examples && $(MAKE)

coq:
	cd arrow-lib && $(MAKE) coq
	cd cava && $(MAKE) coq
	cd monad-examples && $(MAKE) coq
	cd arrow-examples && $(MAKE) coq

clean:
	cd arrow-lib && $(MAKE) clean
	cd cava && $(MAKE) clean
	cd monad-examples && $(MAKE) clean
	cd monad-examples/xilinx && $(MAKE) clean
	cd tests/xilinx && $(MAKE) clean
	cd arrow-examples && $(MAKE) clean
	rm -rf .DS_Store
