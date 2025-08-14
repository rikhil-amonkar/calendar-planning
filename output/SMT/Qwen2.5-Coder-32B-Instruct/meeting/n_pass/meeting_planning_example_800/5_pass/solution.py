# Define the start time at Union Square
start_time = 9 * 60  # 9:00 AM

# Define the people and their availability
people = {
    "Melissa": {"location": "The Castro", "start": 2015, "end": 2115, "duration": 30},
    "Kimberly": {"location": "North Beach", "start": 700, "end": 1030, "duration": 15},
    "Joseph": {"location": "Embarcadero", "start": 1530, "end": 1930, "duration": 75},
    "Barbara": {"location": "Alamo Square", "start": 2045, "end": 2145, "duration": 15},
    "Kenneth": {"location": "Nob Hill", "start": 1215, "end": 1715, "duration": 105},
    "Joshua": {"location": "Presidio", "start": 1630, "end": 1815, "duration": 105},
    "Brian": {"location": "Fisherman's Wharf", "start": 930, "end": 1530, "duration": 45},
    "Steven": {"location": "Mission District", "start": 1930, "end": 2100, "duration": 90},
    "Betty": {"location": "Haight-Ashbury", "start": 1900, "end": 2030, "duration": 90}
}

# Define the travel times
travel_times = {
    "Union Square": {"The Castro": 17, "North Beach": 10, "Embarcadero": 11, "Alamo Square": 15, "Nob Hill": 9, "Presidio": 24, "Fisherman's Wharf": 15, "Mission District": 14, "Haight-Ashbury": 18},
    "The Castro": {"Union Square": 19, "North Beach": 20, "Embarcadero": 22, "Alamo Square": 8, "Nob Hill": 16, "Presidio": 20, "Fisherman's Wharf": 24, "Mission District": 7, "Haight-Ashbury": 6},
    "North Beach": {"Union Square": 7, "The Castro": 23, "Embarcadero": 6, "Alamo Square": 16, "Nob Hill": 7, "Presidio": 17, "Fisherman's Wharf": 5, "Mission District": 18, "Haight-Ashbury": 18},
    "Embarcadero": {"Union Square": 10, "The Castro": 25, "North Beach": 5, "Alamo Square": 19, "Nob Hill": 10, "Presidio": 20, "Fisherman's Wharf": 6, "Mission District": 20, "Haight-Ashbury": 21},
    "Alamo Square": {"Union Square": 14, "The Castro": 8, "North Beach": 15, "Embarcadero": 16, "Nob Hill": 11, "Presidio": 17, "Fisherman's Wharf": 19, "Mission District": 10, "Haight-Ashbury": 5},
    "Nob Hill": {"Union Square": 7, "The Castro": 17, "North Beach": 8, "Embarcadero": 9, "Alamo Square": 11, "Presidio": 17, "Fisherman's Wharf": 10, "Mission District": 13, "Haight-Ashbury": 13},
    "Presidio": {"Union Square": 22, "The Castro": 21, "North Beach": 18, "Embarcadero": 20, "Alamo Square": 19, "Nob Hill": 18, "Fisherman's Wharf": 17, "Mission District": 26, "Haight-Ashbury": 15},
    "Fisherman's Wharf": {"Union Square": 13, "The Castro": 27, "North Beach": 6, "Embarcadero": 8, "Alamo Square": 21, "Nob Hill": 11, "Presidio": 17, "Mission District": 22, "Haight-Ashbury": 22},
    "Mission District": {"Union Square": 15, "The Castro": 7, "North Beach": 17, "Embarcadero": 19, "Alamo Square": 11, "Nob Hill": 12, "Presidio": 25, "Fisherman's Wharf": 22, "Haight-Ashbury": 12},
    "Haight-Ashbury": {"Union Square": 19, "The Castro": 6, "North Beach": 19, "Embarcadero": 20, "Alamo Square": 5, "Nob Hill": 15, "Presidio": 15, "Fisherman's Wharf": 23, "Mission District": 11}
}

# Convert times to minutes since start of the day
def time_to_minutes(time):
    return int(str(time)[:2]) * 60 + int(str(time)[2:])

# Manually order the meetings based on the availability and travel times
ordered_people = ["Kimberly", "Brian", "Joseph", "Kenneth", "Joshua", "Steven", "Betty", "Melissa"]

# Initialize the current time
current_time = start_time

# Create the itinerary
itinerary = []
for person in ordered_people:
    details = people[person]
    location = details["location"]
    start = time_to_minutes(details["start"])
    end = time_to_minutes(details["end"])
    duration = details["duration"]
    
    # Ensure the meeting starts after the current time and respects the person's availability
    meeting_start = max(current_time + travel_times["Union Square" if not itinerary else itinerary[-1]["location"]][location], start)
    meeting_end = meeting_start + duration
    
    # Ensure the meeting ends before the person's availability ends
    if meeting_end <= end:
        itinerary.append({"action": "meet", "person": person, "start_time": f"{meeting_start // 60:02}:{meeting_start % 60:02}", "end_time": f"{meeting_end // 60:02}:{meeting_end % 60:02}"})
        current_time = meeting_end
    else:
        print(f"Cannot meet {person} within their availability.")
        break

# Print the itinerary
print({"itinerary": itinerary})