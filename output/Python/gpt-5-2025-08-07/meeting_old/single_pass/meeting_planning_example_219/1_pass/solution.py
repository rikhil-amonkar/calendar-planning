SOLUTION:
This Python program computes the optimal meeting schedule based on travel times and availability constraints.
It enumerates possible meeting sequences, verifies feasibility with travel times,
and selects the schedule that meets the maximum number of friends, with tie-breakers on total meeting time,
then minimal travel time, then earliest finish time. It outputs the itinerary as JSON.