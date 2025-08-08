# Manually constructed feasible schedule
itinerary = [
    {"action": "meet", "person": "Betty", "start_time": "10:15", "end_time": "10:30"},
    {"action": "meet", "person": "David", "start_time": "13:00", "end_time": "14:30"},
    {"action": "meet", "person": "Barbara", "start_time": "15:00", "end_time": "17:00"}
]

# Print the itinerary in the required JSON format
print({"itinerary": itinerary})