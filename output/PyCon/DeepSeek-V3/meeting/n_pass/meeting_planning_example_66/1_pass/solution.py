import constraint
import json
from datetime import datetime, timedelta

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    if isinstance(time_str, str):
        dt = datetime.strptime(time_str, "%H:%M")
    else:
        dt = time_str
    return dt.hour * 60 + dt.minute

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Input parameters
    start_location = "Nob Hill"
    start_time = "9:00"
    friend_name = "Robert"
    friend_location = "Presidio"
    friend_available_start = "11:15"
    friend_available_end = "17:45"
    min_meeting_duration = 120  # minutes
    travel_to_presidio = 17  # minutes
    travel_from_presidio = 18  # minutes
    
    # Convert times to minutes
    start_minutes = time_to_minutes(start_time)
    friend_start_minutes = time_to_minutes(friend_available_start)
    friend_end_minutes = time_to_minutes(friend_available_end)
    
    # Create problem
    problem = constraint.Problem()
    
    # Variables: departure time from Nob Hill and meeting duration
    problem.addVariable("departure_time", range(start_minutes, friend_end_minutes - min_meeting_duration - travel_to_presidio + 1))
    problem.addVariable("meeting_duration", range(min_meeting_duration, friend_end_minutes - friend_start_minutes + 1))
    
    # Constraints
    def meeting_constraints(departure, duration):
        # Arrival at Presidio
        arrival_at_presidio = departure + travel_to_presidio
        
        # Meeting must start after friend is available
        if arrival_at_presidio < friend_start_minutes:
            return False
            
        # Meeting end time
        meeting_end = arrival_at_presidio + duration
        
        # Meeting must end before friend leaves
        if meeting_end > friend_end_minutes:
            return False
            
        # Return to Nob Hill
        return_to_nob_hill = meeting_end + travel_from_presidio
        
        # We need to return by end of day (optional constraint)
        if return_to_nob_hill > time_to_minutes("23:59"):
            return False
            
        return True
    
    problem.addConstraint(meeting_constraints, ["departure_time", "meeting_duration"])
    
    # Find all solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution with exact constraints, try to find maximum possible meeting time
        max_possible_meeting = friend_end_minutes - max(friend_start_minutes, start_minutes + travel_to_presidio)
        if max_possible_meeting > 0:
            actual_meeting = min(max_possible_meeting, min_meeting_duration)
            best_departure = max(start_minutes, friend_start_minutes - travel_to_presidio)
            
            arrival_at_presidio = best_departure + travel_to_presidio
            meeting_end = arrival_at_presidio + actual_meeting
            return_to_nob_hill = meeting_end + travel_from_presidio
            
            itinerary = [
                {"action": "travel", "location": "Nob Hill to Presidio", "person": "Self", "start_time": minutes_to_time(best_departure), "end_time": minutes_to_time(arrival_at_presidio)},
                {"action": "meet", "location": friend_location, "person": friend_name, "start_time": minutes_to_time(arrival_at_presidio), "end_time": minutes_to_time(meeting_end)},
                {"action": "travel", "location": "Presidio to Nob Hill", "person": "Self", "start_time": minutes_to_time(meeting_end), "end_time": minutes_to_time(return_to_nob_hill)}
            ]
            
            result = {"itinerary": itinerary}
            print(json.dumps(result, indent=2))
            return
        
        # No possible meeting
        result = {"itinerary": []}
        print(json.dumps(result, indent=2))
        return
    
    # Find the solution with maximum meeting duration
    best_solution = max(solutions, key=lambda x: x["meeting_duration"])
    
    departure_time = best_solution["departure_time"]
    meeting_duration = best_solution["meeting_duration"]
    
    # Calculate all time points
    arrival_at_presidio = departure_time + travel_to_presidio
    meeting_end = arrival_at_presidio + meeting_duration
    return_to_nob_hill = meeting_end + travel_from_presidio
    
    # Build itinerary
    itinerary = [
        {"action": "travel", "location": "Nob Hill to Presidio", "person": "Self", "start_time": minutes_to_time(departure_time), "end_time": minutes_to_time(arrival_at_presidio)},
        {"action": "meet", "location": friend_location, "person": friend_name, "start_time": minutes_to_time(arrival_at_presidio), "end_time": minutes_to_time(meeting_end)},
        {"action": "travel", "location": "Presidio to Nob Hill", "person": "Self", "start_time": minutes_to_time(meeting_end), "end_time": minutes_to_time(return_to_nob_hill)}
    ]
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()