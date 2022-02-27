#!/bin/bash

do_debug=0
if [[ "x--debug" = "x$1" ]]; then
  do_debug=1
fi

hdr_files=( $(find src/ -type f -name '*.h') )
src_files=( $(find src/ -type f -name '*.c') )

# Let's get the maximum lengths first, so we can have prettier output
max_file_len=0
max_meso_len=0
max_path_len=0
h_dir="none"

for hdr in "${hdr_files[@]}" ; do
  cur_dir="$(dirname $hdr)"
  cur_len=$(echo -n "$hdr" | wc -c)

  if [[ $cur_len -gt $max_file_len ]]; then
    max_file_len=$cur_len
  fi

  # Also check path lengths
  if [[ $h_dir != $cur_dir ]]; then
    h_dir=$cur_dir
    cur_len=$(echo -n "$h_dir" | wc -c)
    if [[ $cur_len -gt $max_path_len ]]; then
      max_path_len=$cur_len
      ## <path>/meson.build = path len + 12
      max_meso_len=$((cur_len+12))
    fi
  fi
done


for hdr in "${hdr_files[@]}" ; do
	h_dir="$(dirname $hdr)"
	h_file="$(basename $hdr .h)"
	m_file="${h_dir}/meson.build"

  if [[ $do_debug -eq 1 ]]; then
    printf "%-${max_file_len}s : " "$hdr"
  fi

	# Is it listed in any meson.build?
	if [[ -f ${m_file} ]]; then
    if [[ 0 -lt $(grep -c "${h_file}.c" ${m_file}) ]] || \
       [[ 0 -lt $(grep -c "${h_file}.h" ${m_file}) ]]; then
      # It is needed.
      if [[ $do_debug -eq 1 ]]; then
        printf "Included in %-${max_meso_len}s\n" "$m_file"
      fi
      continue 1
    fi
  fi

	# Is it included in any source files?
	for src in "${src_files[@]}" ; do
		is_inc=$(grep -P '^#include' $src | grep -c "${h_file}.h")
		if [[ 0 -lt $is_inc ]]; then
			# it is indeed
      if [[ $do_debug -eq 1 ]]; then
      	if [[ -f ${m_file} ]]; then
          printf "Included in %-${max_file_len}s but not listed in %-${max_meso_len}s\n" "$src" "$m_file"
        else
          printf "Included in %-${max_file_len}s\n" "$src"
        fi
      fi
			continue 2
		fi
	done

	# Is it included in any header files?
	for src in "${hdr_files[@]}" ; do

	  # If we already removed the header, or if it is the checked file, continue
	  if [[ ! -f $src || $src = $hdr ]]; then
	    continue 1
    fi

		is_inc=$(grep '#include' $src | grep -c "${h_file}.h")
		if [[ 0 -lt $is_inc ]]; then
			# it is indeed
      if [[ $do_debug -eq 1 ]]; then
        if [[ -f ${m_file} ]]; then
          printf "Included in %-${max_file_len}s but not listed in %-${max_meso_len}s\n" "$src" "$m_file"
        else
          printf "Included in %-${max_file_len}s\n" "$src"
        fi
      fi
			continue 2
		fi
	done

	# As it was not included, remove it.
  if [[ $do_debug -eq 1 ]]; then
  	echo "Nowhere listed, removing...	git rm -f $hdr"
  else
    printf "%-${max_file_len}s nowhere listed, removing...\n" "$hdr"
    git rm -f $hdr
  fi
done
