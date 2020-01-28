#!/bin/bash
#
# Chris Cannam, 2015-2018. MIT licence

# Disable shellcheck warnings for useless-use-of-cat. UUOC is good
# practice, not bad: clearer, safer, less error-prone.
# shellcheck disable=SC2002

debug=no

if [ -z "${SML_LIB:-}" ]; then
    lib=/usr/lib/mlton/sml
    if [ ! -d "$lib" ]; then
	lib=/usr/local/lib/mlton/sml
    fi
else
    lib="$SML_LIB"
fi

canonicalise() {
    local pre="$1"
    local post=""
    while [ "$pre" != "$post" ]; do
        if [ -z "$post" ]; then post="$pre"; else pre="$post"; fi
        post=$(echo "$post" | sed -e 's|[^/.][^/.]*/\.\./||g')
    done
    echo "$post" | sed -e 's|^./||' -e 's|//|/|g'
}

simplify() {
    local path="$1"
    simple=$(canonicalise "$path")
    if [ "$debug" = "yes" ]; then
	echo "simplified \"$path\" to \"$simple\"" 1>&2
    fi
    if [ ! -f "$simple" ]; then
	echo "*** Error: input file \"$simple\" not found" 1>&2
        exit 1
    fi
    echo "$simple"
}

cat_mlb() {
    local mlb=$(simplify "$1")
    if [ ! -f "$mlb" ]; then exit 1; fi
    local dir
    dir=$(dirname "$mlb")
    if [ "$debug" = "yes" ]; then
	echo "reading MLB file \"$mlb\":" 1>&2
    fi
    cat "$mlb" | while read -r line; do
        if [ "$debug" = "yes" ]; then
	    echo "read line \"$line\":" 1>&2
        fi
	local trimmed
	trimmed=$(
	    # shellcheck disable=SC2016
	    echo "$line" | 
		sed 's|(\*.*\*)||' |              # remove ML-style comments
		sed 's#$(SML_LIB)#'"${lib}"'#g' | # expand library path
		perl -p -e 's|\$\(([A-Za-z_-]+)\)|$ENV{$1}|' | # expand other vars
		sed 's|^ *||' |                   # remove leading whitespace
		sed 's|[[:space:]]*$||')          # remove trailing whitespace
	local path="$trimmed"
	case "$path" in
	    "") ;;		                  # keep empty lines for ignoring later
	    /*) ;;
	    *) path="$dir/$trimmed" ;;
	esac
	case "$path" in
	    "") ;;		                  # ignore empty lines
	    *basis.mlb) ;;			  # remove incompatible Basis lib
	    *mlton.mlb) ;;			  # remove incompatible MLton lib
	    *main.sml) ;;			  # remove redundant call to main
	    *.mlb) cat_mlb "$path" ;;
	    *.sml) simplify "$path" ;;
	    *.sig) simplify "$path" ;;
            *) echo "*** Warning: unsupported syntax or file in $mlb: $trimmed" 1>&2
	esac
    done
    if [ "$debug" = "yes" ]; then
	echo "finished reading MLB file \"$mlb\"" 1>&2
    fi
}

expand_arg() {
    local arg="$1"
    case "$arg" in
	*.sml) echo "$arg" ;;
	*.mlb) cat_mlb "$arg" ;;
	*) echo "*** Error: .sml or .mlb file must be provided" 1>&2
	   exit 1 ;;
    esac
}

get_base() {
    local arg="$1"
    case "$arg" in
	*.sml) basename "$arg" .sml ;;
	*.mlb) basename "$arg" .mlb ;;
	*) echo "*** Error: .sml or .mlb file must be provided" 1>&2
	   exit 1 ;;
    esac
}    

get_outfile() {
    local arg="$1"
    canonicalise $(dirname "$arg")/$(get_base "$arg")
}

get_tmpfile() {
    local arg="$1"
    mktemp /tmp/smlbuild-$(get_base "$arg")-XXXXXXXX
}

get_tmpsmlfile() {
    local arg="$1"
    mktemp /tmp/smlbuild-$(get_base "$arg")-XXXXXXXX.sml
}

get_tmpobjfile() {
    local arg="$1"
    mktemp /tmp/smlbuild-$(get_base "$arg")-XXXXXXXX.o
}


