#!/bin/bash

folder="experiment_results/sample_info" #specify the folder on which to run on
num_workers=4 #specify the number of cores to be used
time_out=3600 #specify the timeout for the tools
queue_name="Sample-experiments"
wait_time=10 #wait time for letting compilation happen without interruption

while getopts f:w:n:t: flag
do
    case "${flag}" in
        f) folder=${OPTARG};;
        w) num_workers=${OPTARG};;
    	t) time_out=${OPTARG};;
    esac
done


pkill rq > /dev/null 2>&1
python q_sample_sizes.py --output_folder $folder --timeout $time_out

for ((i=0;i<$num_workers;i+=1));
do
	rq worker -b -q $queue_name &
done

sleep 2
while [ true ]
do
	worker_status=$(rq info -W | grep -oP "[0-9]*.(workers)")
	read -a strarr1 <<< $worker_status
	remaining_workers=${strarr1[0]}
	
	queue_status=$(rq info -Q -r $queue_name &)
	read -a strarr2 <<< $queue_status
	remaining_in_queue=${strarr2[2]}

	remaining_tasks=$(expr $remaining_workers + $remaining_in_queue)
	echo "Remaining tasks $remaining_tasks"

	if [[ $remaining_workers -eq 0 ]]
	then
		sleep $wait_time
		python q_sample_sizes.py --output_folder $folder --timeout $time_out --compile
		break
	fi
	sleep $wait_time
done

pkill cvc4