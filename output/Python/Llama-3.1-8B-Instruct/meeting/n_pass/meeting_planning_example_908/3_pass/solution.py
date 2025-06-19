import json
from datetime import timedelta

# Assuming these variables are defined elsewhere in your code
start_time = '08:00'  # replace with your actual start time
travel_distances = {'Fisherman\'s Wharf': {'The Castro': 10}}  # replace with your actual travel distances
constraints = {'Brian': {'duration': 30}}  # replace with your actual constraints

# Create the dictionary correctly
meeting_brian = {
    'action':'meet',
    'location': 'The Castro',
    'person': 'Brian',
   'start_time': start_time,
    'end_time': (timedelta(minutes=travel_distances['Fisherman\'s Wharf']['The Castro'] + constraints['Brian']['duration'])).strftime('%H:%M')
}

# Convert the dictionary to a string
meeting_brian_str = json.dumps(meeting_brian)

print(meeting_brian_str)