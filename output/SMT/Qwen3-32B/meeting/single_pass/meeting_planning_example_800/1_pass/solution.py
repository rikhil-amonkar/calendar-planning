from z3 import *
import json

# Define travel times between locations
travel_times = {
    "Union Square to The Castro": 17,
    "Union Square to North Beach": 10,
    "Union Square to Embarcadero": 11,
    "Union Square to Alamo Square": 15,
    "Union Square to Nob Hill": 9,
    "Union Square to Presidio": 24,
    "Union Square to Fisherman's Wharf": 15,
    "Union Square to Mission District": 14,
    "Union Square to Haight-Ashbury": 18,
    "The Castro to Union Square": 19,
    "The Castro to North Beach": 20,
    "The Castro to Embarcadero": 22,
    "The Castro to Alamo Square": 8,
    "The Castro to Nob Hill": 16,
    "The Castro to Presidio": 20,
    "The Castro to Fisherman's Wharf": 24,
    "The Castro to Mission District": 7,
    "The Castro to Haight-Ashbury": 6,
    "North Beach to Union Square": 7,
    "North Beach to The Castro": 23,
    "North Beach to Embarcadero": 6,
    "North Beach to Alamo Square": 16,
    "North Beach to Nob Hill": 7,
    "North Beach to Presidio": 17,
    "North Beach to Fisherman's Wharf": 5,
    "North Beach to Mission District": 18,
    "North Beach to Haight-Ashbury": 18,
    "Embarcadero to Union Square": 10,
    "Embarcadero to The Castro": 25,
    "Embarcadero to North Beach": 5,
    "Embarcadero to Alamo Square": 19,
    "Embarcadero to Nob Hill": 10,
    "Embarcadero to Presidio": 20,
    "Embarcadero to Fisherman's Wharf": 6,
    "Embarcadero to Mission District": 20,
    "Embarcadero to Haight-Ashbury": 21,
    "Alamo Square to Union Square": 14,
    "Alamo Square to The Castro": 8,
    "Alamo Square to North Beach": 15,
    "Alamo Square to Embarcadero": 16,
    "Alamo Square to Nob Hill": 11,
    "Alamo Square to Presidio": 17,
    "Alamo Square to Fisherman's Wharf": 19,
    "Alamo Square to Mission District": 10,
    "Alamo Square to Haight-Ashbury": 5,
    "Nob Hill to Union Square": 7,
    "Nob Hill to The Castro": 17,
    "Nob Hill to North Beach": 8,
    "Nob Hill to Embarcadero": 9,
    "Nob Hill to Alamo Square": 11,
    "Nob Hill to Presidio": 17,
    "Nob Hill to Fisherman's Wharf": 10,
    "Nob Hill to Mission District": 13,
    "Nob Hill to Haight-Ashbury": 13,
    "Presidio to Union Square": 22,
    "Presidio to The Castro": 21,
    "Presidio to North Beach": 18,
    "Presidio to Embarcadero": 20,
    "Presidio to Alamo Square": 19,
    "Presidio to Nob Hill": 18,
    "Presidio to Fisherman's Wharf": 19,
    "Presidio to Mission District": 26,
    "Presidio to Haight-Ashbury": 15,
    "Fisherman's Wharf to Union Square": 13,
    "Fisherman's Wharf to The Castro": 27,
    "Fisherman's Wharf to North Beach": 6,
    "Fisherman's Wharf to Embarcadero": 8,
    "Fisherman's Wharf to Alamo Square": 21,
    "Fisherman's Wharf to Nob Hill": 11,
    "Fisherman's Wharf to Presidio": 17,
    "Fisherman's Wharf to Mission District": 22,
    "Fisherman's Wharf to Haight-Ashbury": 22,
    "Mission District to Union Square": 15,
    "Mission District to The Castro": 7,
    "Mission District to North Beach": 17,
    "Mission District to Embarcadero": 19,
    "Mission District to Alamo Square": 11,
    "Mission District to Nob Hill": 12,
    "Mission District to Presidio": 25,
    "Mission District to Fisherman's Wharf": 22,
    "Mission District to Haight-Ashbury": 12,
    "Haight-Ashbury to Union Square": 19,
    "Haight-Ashbury to The Castro": 6,
    "Haight-Ashbury to North Beach": 19,
    "Haight-Ashbury to Embarcadero": 20,
    "Haight-Ashbury to Alamo Square": 5,
    "Haight-Ashbury to Nob Hill": 15,
    "Haight-Ashbury to Presidio": 15,
    "Haight-Ashbury to Fisherman's Wharf": 23,
    "Haight-Ashbury to Mission District": 11,
}

# Define friends' data (converted to minutes since midnight)
friends_data = {
    'Kimberly': {'location': 'North Beach', 'available_start': 7*60, 'available_end': 10*60+30, 'required': 15},
    'Brian': {'location': 'Fisherman\'s Wharf', 'available_start': 9*60+30, 'available_end': 15*60+30, 'required': 45},
    'Kenneth': {'location': 'Nob Hill', 'available_start': 12*60+15, 'available_end': 17*60+15, 'required': 105},
    'Joseph': {'location': 'Embarcadero', 'available_start': 15*60+30, 'available_end': 19*60+30, 'required': 75},
    'Betty': {'location': 'Haight-Ashbury', 'available_start': 19*60, 'available_end': 20*60+30, 'required': 90},
    'Melissa': {'location': 'The Castro', 'available_start': 20*60+15, 'available_end': 21*60+15, 'required': 30},
    'Barbara': {'location': 'Alamo Square', 'available_start': 20*60+45, 'available_end': 21*60+45, 'required': 15},
}

# Define the sequence of friends to meet
sequence = ['Kimberly', 'Brian', 'Kenneth', 'Joseph', 'Betty', 'Melissa', 'Barbara']

# Create solver
s = Solver()

# Define variables for each meeting's start and end times
start_times = []
end_times = []
prev_end = 540  # Start at Union Square at 9:00 AM (540 minutes)

for friend in sequence:
    loc = friends_data[friend]['location']
    required = friends_data[friend]['required']
    available_start = friends_data[friend]['available_start']
    available_end = friends_data[friend]['available_end']
    
    # Create variables for start and end times
    start = Int(f"{friend}_start")
    end = Int(f"{friend}_end")
    start_times.append(start)
    end_times.append(end)
    
    # Add constraints for this meeting
    # Duration constraint
    s.add(end == start + required)
    # Available time window
    s.add(start >= available_start)
    s.add(end <= available_end)
    
    # Travel time from previous location to this location
    if sequence.index(friend) == 0:
        # First friend: previous location is Union Square
        prev_loc = 'Union Square'
    else:
        prev_loc = friends_data[sequence[sequence.index(friend)-1]]['location']
    
    # Get travel time from previous location to current location
    travel_time = travel_times[f"{prev_loc} to {loc}"]
    
    # Constraint: start >= prev_end + travel_time
    s.add(start >= prev_end + travel_time)
    
    # Update prev_end to this meeting's end time
    prev_end = end

# Check if the constraints are satisfiable
if s.check() == sat:
    m = s.model()
    # Extract the times and convert to HH:MM format
    itinerary = []
    for i, friend in enumerate(sequence):
        start = m[start_times[i]].as_long()
        end = m[end_times[i]].as_long()
        # Convert to HH:MM
        start_h = start // 60
        start_m = start % 60
        end_h = end // 60
        end_m = end % 60
        start_time = f"{start_h:02d}:{start_m:02d}"
        end_time = f"{end_h:02d}:{end_m:02d}"
        itinerary.append({"action": "meet", "person": friend, "start_time": start_time, "end_time": end_time})
    print(json.dumps({"itinerary": itinerary}))
else:
    print("No solution found.")