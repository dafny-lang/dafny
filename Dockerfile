FROM mcr.microsoft.com/dotnet/core/sdk:3.1-bionic AS build
WORKDIR /build
RUN apt-get update \
    && apt-get install -y unzip \
    && rm -rf /var/lib/apt/lists/*
#RUN wget https://github.com/Z3Prover/z3/releases/download/z3-4.8.4/z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04.zip \
COPY z3-4.8.4.d6df51951f4c-x64-ubuntu-16.04.zip .
RUN pwd \
    && unzip z3*.zip \
    && rm z3*.zip \
    && mv z3* z3
COPY dafny ./dafny
COPY Source ./Source
RUN dotnet restore Source/DafnyLS.sln
RUN dotnet build --configuration Release --no-restore Source/DafnyLS.sln
RUN cp -r z3 Source/DafnyLS/bin/Release/netcoreapp3.1/z3

FROM mcr.microsoft.com/dotnet/core/aspnet:3.1-bionic AS runtime
WORKDIR /app
COPY --from=build /build/Source/DafnyLS/bin/Release/netcoreapp3.1 .
RUN chmod +x DafnyLS \
    && chmod +x z3/bin/z3
CMD [ "./DafnyLS" ]
