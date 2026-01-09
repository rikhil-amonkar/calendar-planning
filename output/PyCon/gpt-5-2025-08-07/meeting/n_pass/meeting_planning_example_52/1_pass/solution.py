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
    barbara_location = "Richmond District"
    barbara_available_start = "13:15"
    barbara_available_end = "18:15"
    min_meeting_duration = 45
    travel_to_richmond = 14
    travel_to_russian_hill = 13
    
    # Convert times to minutes
    start_minutes = time_to_minutes(start_time)
    barbara_start_minutes = time_to_minutes(barbara_available_start)
    barbara_end_minutes = time_to_minutes(barbara_available_end)
    
    # Create constraint problem
    problem = Problem()
    
    # Variables: meeting start time and end time (in minutes)
    problem.addVariable("meeting_start", range(barbara_start_minutes, barbara_end_minutes - min_meeting_duration + 1))
    problem.addVariable("meeting_end", range(barbara_start_minutes + min_meeting_duration, barbara_end_minutes + 1))
    
    # Constraints
    def meeting_duration_constraint(start, end):
        return end - start >= min_meeting_duration
    
    def travel_constraint(start, end):
        # Must have time to travel to Richmond and back
        travel_to = start_minutes + travel_to_richmond <= start
        travel_back = end + travel_to_russian_hill <= 24 * 60  # Before midnight
        return travel_to and travel_back
    
    problem.addConstraint(meeting_duration_constraint, ["meeting_start", "meeting_end"])
    problem.addConstraint(travel_constraint, ["meeting_start", "meeting_end"])
    
    # Find all possible solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution found with full duration, try to find maximum possible meeting time
        max_possible_duration = min(
            barbara_end_minutes - barbara_start_minutes,
            (24 * 60 - travel_to_russian_hill) - barbara_start_minutes
        )
        
        if max_possible_duration > 0:
            actual_duration = min(max_possible_duration, min_meeting_duration)
            meeting_start = barbara_start_minutes
            meeting_end = barbara_start_minutes + actual_duration
            solutions = [{"meeting_start": meeting_start, "meeting_end": meeting_end}]
    
    if solutions:
        # Choose the solution that maximizes meeting duration
        best_solution = max(solutions, key=lambda s: s["meeting_end"] - s["meeting_start"])
        
        # Build itinerary
        itinerary = []
        
        # Add travel to Richmond District
        travel_start_time = minutes_to_time(start_minutes)
        travel_end_time = minutes_to_time(best_solution["meeting_start"])
        itinerary.append({
            "action": "travel",
            "location": "Richmond District",
            "person": "None",
            "start_time": travel_start_time,
            "end_time": travel_end_time
        })
        
        # Add meeting with Barbara
        meeting_start_time = minutes_to_time(best_solution["meeting_start"])
        meeting_end_time = minutes_to_time(best_solution["meeting_end"])
        itinerary.append({
            "action": "meet",
            "location": "Richmond District",
            "person": "Barbara",
            "start_time": meeting_start_time,
            "end_time": meeting_end_time
        })
        
        # Add travel back to Russian Hill
        travel_back_start = minutes_to_time(best_solution["meeting_end"])
        travel_back_end = minutes_to_time(best_solution["meeting_end"] + travel_to_russian_hill)
        itinerary.append({
            "action": "travel",
            "location": "Russian Hill",
            "person": "None",
            "start_time": travel_back_start,
            "end_time": travel_back_end
        })
        
        result = {"itinerary": itinerary}
    else:
        result = {"itinerary": []}
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()