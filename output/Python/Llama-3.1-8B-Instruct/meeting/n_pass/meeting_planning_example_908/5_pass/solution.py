import json
from datetime import datetime, timedelta

# Assuming these variables are defined elsewhere in your code
start_time_str = '08:00'  # replace with your actual start time
travel_distances = {'Fisherman\'s Wharf': {'The Castro': 10}}  # replace with your actual travel distances
constraints = {'Brian': {'duration': 30}}  # replace with your actual constraints

# Convert start time string to datetime object
start_time = datetime.strptime(start_time_str, '%H:%M')

# Calculate the end time of the meeting by adding the travel time and the meeting duration
end_time = start_time + timedelta(minutes=constraints['Brian']['duration'])

# Create the dictionary correctly
meeting_brian = {
    'action':'meet',
    'location': 'The Castro',
    'person': 'Brian',
   'start_time': start_time.strftime('%H:%M'),
    'end_time': end_time.strftime('%H:%M')
}

# Convert the dictionary to a string
meeting_brian_str = json.dumps(meeting_brian)

print(meeting_brian_str)