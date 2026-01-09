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
    # Define travel times
    park_to_chinatown = 23
    chinatown_to_park = 23
    
    # Define constraints
    arrival_time = time_to_minutes("9:00")
    david_start = time_to_minutes("16:00")
    david_end = time_to_minutes("21:45")
    min_meeting_duration = 105
    
    # Create problem instance
    problem = Problem()
    
    # Define variables: meeting start time and end time with David
    problem.addVariable("meeting_start", range(david_start, david_end - min_meeting_duration + 1))
    problem.addVariable("meeting_end", range(david_start + min_meeting_duration, david_end + 1))
    
    # Constraints
    def meeting_constraint(start, end):
        # Meeting must be at least min_meeting_duration
        return end - start >= min_meeting_duration
    
    def travel_constraint(start, end):
        # Must have time to travel from park to chinatown before meeting
        # and from chinatown to park after meeting
        travel_before = start - park_to_chinatown
        travel_after = end + chinatown_to_park
        
        # Must arrive at park before starting travel to chinatown
        # and the entire schedule must fit within the day
        return travel_before >= arrival_time and travel_after <= 24 * 60
    
    problem.addConstraint(meeting_constraint, ["meeting_start", "meeting_end"])
    problem.addConstraint(travel_constraint, ["meeting_start", "meeting_end"])
    
    # Find all solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution found with minimum duration, try to find any meeting
        problem = Problem()
        max_possible_duration = david_end - david_start - park_to_chinatown - chinatown_to_park
        if max_possible_duration > 0:
            actual_duration = min(min_meeting_duration, max_possible_duration)
            problem.addVariable("meeting_start", [david_start])
            problem.addVariable("meeting_end", [david_start + actual_duration])
            solutions = problem.getSolutions()
    
    if solutions:
        # Use the first valid solution
        solution = solutions[0]
        meeting_start = solution["meeting_start"]
        meeting_end = solution["meeting_end"]
        
        # Build itinerary
        itinerary = [
            {
                "action": "travel",
                "location": "Golden Gate Park to Chinatown",
                "person": "Self",
                "start_time": minutes_to_time(meeting_start - park_to_chinatown),
                "end_time": minutes_to_time(meeting_start)
            },
            {
                "action": "meet",
                "location": "Chinatown",
                "person": "David",
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            },
            {
                "action": "travel",
                "location": "Chinatown to Golden Gate Park",
                "person": "Self",
                "start_time": minutes_to_time(meeting_end),
                "end_time": minutes_to_time(meeting_end + chinatown_to_park)
            }
        ]
        
        result = {
            "itinerary": itinerary
        }
    else:
        result = {
            "itinerary": [],
            "error": "No valid schedule found that meets all constraints"
        }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()