import json
from datetime import datetime, timedelta

# Define travel times
travel_times = {
    "Embarcadero": {"Richmond District": 21, "Union Square": 10, "Financial District": 5, "Pacific Heights": 11, "Nob Hill": 10, "Bayview": 21},
    "Richmond District": {"Embarcadero": 19, "Union Square": 21, "Financial District": 22, "Pacific Heights": 10, "Nob Hill": 17, "Bayview": 26},
    "Union Square": {"Embarcadero": 11, "Richmond District": 20, "Financial District": 9, "Pacific Heights": 15, "Nob Hill": 9, "Bayview": 15},
    "Financial District": {"Embarcadero": 4, "Richmond District": 21, "Union Square": 9, "Pacific Heights": 13, "Nob Hill": 8, "Bayview": 19},
    "Pacific Heights": {"Embarcadero": 10, "Richmond District": 12, "Union Square": 12, "Financial District": 13, "Nob Hill": 8, "Bayview": 22},
    "Nob Hill": {"Embarcadero": 9, "Richmond District": 14, "Union Square": 7, "Financial District": 9, "Pacific Heights": 8, "Bayview": 19},
    "Bayview": {"Embarcadero": 19, "Richmond District": 25, "Union Square": 17, "Financial District": 19, "Pacific Heights": 23, "Nob Hill": 20}
}

# Define availability constraints
availability = {
    "Kenneth": ("21:15", "22:00", 30),
    "Lisa": ("09:00", "16:30", 45),
    "Joshua": ("12:00", "15:15", 15),
    "Nancy": ("08:00", "11:30", 90),
    "Andrew": ("11:30", "20:15", 60),
    "John": ("16:45", "21:30", 75)
}

# Convert time strings to minutes since midnight
def time_to_minutes(time_str):
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

# Convert minutes since midnight to time string
def minutes_to_time(minutes):
    hours = minutes // 60
    minutes = minutes % 60
    return f"{hours}:{minutes:02}"

# Check if a meeting can be scheduled
def can_meet(current_time, person):
    start, end, min_duration = availability[person]
    start_minutes = time_to_minutes(start)
    end_minutes = time_to_minutes(end)
    return start_minutes <= current_time <= end_minutes - min_duration

# Recursive function to explore itineraries
def explore_itinerary(current_location, current_time, itinerary):
    global best_itinerary
    current_time_minutes = time_to_minutes(current_time)
    
    # Check if we can meet any of the friends
    for person in availability:
        if can_meet(current_time_minutes, person):
            start_minutes = time_to_minutes(availability[person][0])
            end_minutes = time_to_minutes(availability[person][1])
            min_duration = availability[person][2]
            
            # Calculate the actual meeting time
            meeting_start = max(current_time_minutes, start_minutes)
            meeting_end = min(meeting_start + min_duration, end_minutes)
            
            # If we can have the meeting
            if meeting_start + min_duration <= meeting_end:
                new_itinerary = itinerary + [{
                    "action": "meet",
                    "location": current_location,
                    "person": person,
                    "start_time": minutes_to_time(meeting_start),
                    "end_time": minutes_to_time(meeting_end)
                }]
                
                # Update the best itinerary if this one is better
                if len(new_itinerary) > len(best_itinerary):
                    best_itinerary = new_itinerary
                
                # Explore further from this point
                for next_location in travel_times[current_location]:
                    travel_time = travel_times[current_location][next_location]
                    next_time_minutes = meeting_end + travel_time
                    if next_time_minutes < time_to_minutes("23:59"):
                        explore_itinerary(next_location, minutes_to_time(next_time_minutes), new_itinerary)

# Initialize the best itinerary
best_itinerary = []

# Start exploring from Embarcadero at 9:00 AM
explore_itinerary("Embarcadero", "9:00", [])

# Output the best itinerary as JSON
output = {
    "itinerary": best_itinerary
}
print(json.dumps(output, indent=2))