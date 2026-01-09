from constraint import Problem
import json

def time_to_minutes(time_str):
    """Convert time string (H:MM) to minutes since midnight"""
    hours, minutes = map(int, time_str.split(':'))
    return hours * 60 + minutes

def minutes_to_time(minutes):
    """Convert minutes since midnight to time string (H:MM)"""
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Input parameters
    start_location = "Russian Hill"
    start_time = "9:00"
    barbara_location = "Pacific Heights"
    barbara_available_start = "7:15"
    barbara_available_end = "22:00"  # 10:00 PM in 24-hour format
    min_meeting_duration = 60
    travel_time = 7  # minutes between locations
    
    # Convert times to minutes
    start_time_min = time_to_minutes(start_time)
    barbara_start_min = time_to_minutes(barbara_available_start)
    barbara_end_min = time_to_minutes(barbara_available_end)
    
    # Create constraint problem
    problem = Problem()
    
    # Variables: meeting start time and end time (in minutes)
    # We'll consider discrete time slots in 15-minute intervals for efficiency
    time_slots = range(barbara_start_min, barbara_end_min + 1, 15)
    
    problem.addVariable("meeting_start", time_slots)
    problem.addVariable("meeting_end", time_slots)
    
    # Constraints
    # 1. Meeting duration must be at least min_meeting_duration
    problem.addConstraint(lambda start, end: end - start >= min_meeting_duration, 
                         ["meeting_start", "meeting_end"])
    
    # 2. Meeting must be within Barbara's availability
    problem.addConstraint(lambda start: start >= barbara_start_min, ["meeting_start"])
    problem.addConstraint(lambda end: end <= barbara_end_min, ["meeting_end"])
    
    # 3. We need time to travel from start location to meeting location
    # Since we start at Russian Hill at 9:00 and need to travel to Pacific Heights
    earliest_arrival = start_time_min + travel_time
    problem.addConstraint(lambda start: start >= earliest_arrival, ["meeting_start"])
    
    # Find all possible solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solutions found, create empty itinerary
        result = {"itinerary": []}
    else:
        # Find the earliest possible meeting (optimizing for earliest start)
        best_solution = min(solutions, key=lambda x: x["meeting_start"])
        
        meeting_start_time = minutes_to_time(best_solution["meeting_start"])
        meeting_end_time = minutes_to_time(best_solution["meeting_end"])
        
        # Create itinerary
        itinerary = [
            {
                "action": "travel",
                "location": "Russian Hill to Pacific Heights",
                "person": "Self",
                "start_time": start_time,
                "end_time": minutes_to_time(start_time_min + travel_time)
            },
            {
                "action": "meet",
                "location": barbara_location,
                "person": "Barbara",
                "start_time": meeting_start_time,
                "end_time": meeting_end_time
            }
        ]
        
        result = {"itinerary": itinerary}
    
    # Output as JSON
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()