# Define the manual schedule
schedule = [
    {"action": "meet", "person": "Brian", "start_time": "09:25", "end_time": "10:25"},
    {"action": "meet", "person": "Ashley", "start_time": "10:45", "end_time": "11:30"},
    {"action": "meet", "person": "Joseph", "start_time": "11:45", "end_time": "13:15"},
    {"action": "meet", "person": "Mark", "start_time": "13:30", "end_time": "14:00"},
    {"action": "meet", "person": "Lisa", "start_time": "14:15", "end_time": "15:30"},
    {"action": "meet", "person": "Stephanie", "start_time": "15:45", "end_time": "17:00"},
    {"action": "meet", "person": "Patricia", "start_time": "17:15", "end_time": "19:15"},
    {"action": "meet", "person": "Karen", "start_time": "19:30", "end_time": "21:15"}
]

# Print the schedule in JSON format
print({"itinerary": schedule})