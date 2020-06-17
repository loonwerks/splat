FROM ubuntu:16.04 AS build
RUN apt-get update && apt-get install -y -q \
	build-essential \
	git \
	unzip \
	wget
WORKDIR /
RUN wget -q -O polyml.zip https://github.com/polyml/polyml/archive/v5.8.zip && unzip polyml.zip && rm polyml.zip
WORKDIR /polyml-5.8
RUN ./configure --prefix=/polyml-bin
RUN make && make install

WORKDIR /
RUN git clone -b master --depth 1 https://github.com/HOL-Theorem-Prover/HOL.git HOL
WORKDIR /HOL
RUN /polyml-bin/bin/poly < tools/smart-configure.sml
RUN bin/build

WORKDIR /
RUN git clone --depth 1 https://github.com/loonwerks/splat.git
WORKDIR /splat
RUN /HOL/bin/Holmake

FROM ubuntu:16.04
WORKDIR /
COPY --from=build /polyml-bin/lib/libpolyml.so.10 /polyml-bin/lib/libpolyml.so.10
COPY --from=build /splat/splat /splat/splat
WORKDIR /user
ENV LD_LIBRARY_PATH=/polyml-bin/lib
ENTRYPOINT [ "/splat/splat" ]
CMD []

