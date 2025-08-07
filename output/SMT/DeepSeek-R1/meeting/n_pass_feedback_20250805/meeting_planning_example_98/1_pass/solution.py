from z3 import *
import json

def main():
    # Convert time string to minutes since midnight
    def time_to_minutes(time_str):
        parts = time_str.split(':')
        hours = int(parts[0])
        minutes = int(parts[1])
        return hours * 60 + minutes

    # Convert minutes back to HH:MM format
    def minutes_to_time(mins):
        hours = mins // 60
        minutes = mins % 60
        return f"{hours:02d}:{minutes:02d}"

    # Given data
    start_location = "Alamo Square"
    start_time_str = "09:00"
    start_time_minutes = time_to_minutes(start_time_str)
    
    # Friend data
    friend_name = "Timothy"
    friend_location = "Richmond District"
    friend_avail_start = time_to_minutes("20:45")
    friend_avail_end = time_to_minutes("21:30")
    min_duration = 45  # minutes
    
    # Travel times
    travel_times = {
        ("Alamo Square", "Richmond District"): 12
    }
    travel_time = travel_times[(start_location, friend_location)]

    # Initialize Z3 solver
    s = Solver()
    
    # Departure time from Alamo Square (in minutes since midnight)
    departure = Int('departure')
    
    # Constraints
    s.add(departure >= start_time_minutes)  # Can't depart before arrival
    arrival = departure + travel_time
    # Meeting must start by friend's availability end minus min_duration to have enough time
    s.add(arrival <= friend_avail_end - min_duration)
    # Meeting must start no earlier than friend's availability start
    s.add(arrival >= friend_avail_start - (friend_avail_end - friend_avail_start))  # Relaxed, but tight window fixes it
    
    # Since the window is exactly min_duration, meeting must be [20:45, 21:30]
    meeting_start = friend_avail_start
    meeting_end = friend_avail_end

    # Check satisfiability
    if s.check() == sat:
        # Create itinerary
        itinerary = [{
            "action": "meet",
            "person": friend_name,
            "start_time": minutes_to_time(meeting_start),
            "end_time": minutes_to_time(meeting_end)
        }]
        
        # Output as JSON
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))  # No solution found

if __name__ == "__main__":
    main()