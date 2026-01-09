import constraint
from datetime import datetime, timedelta
import json

def main():
    # Input parameters
    travel_rh_to_richmond = 14
    travel_richmond_to_rh = 13
    
    # Convert times to minutes since midnight for easier computation
    arrival_time = datetime.strptime("9:00", "%H:%M")
    daniel_start = datetime.strptime("19:00", "%H:%M")  # 7:00 PM
    daniel_end = datetime.strptime("20:15", "%H:%M")    # 8:15 PM
    
    arrival_minutes = arrival_time.hour * 60 + arrival_time.minute
    daniel_start_minutes = daniel_start.hour * 60 + daniel_start.minute
    daniel_end_minutes = daniel_end.hour * 60 + daniel_end.minute
    
    min_meeting_duration = 75
    
    # Create problem
    problem = constraint.Problem()
    
    # Variables: start time of meeting with Daniel (in minutes since midnight)
    problem.addVariable('daniel_meeting_start', range(daniel_start_minutes, daniel_end_minutes - min_meeting_duration + 1))
    
    # Constraints
    def travel_and_meeting_constraint(daniel_start_time):
        # Calculate when we need to leave Russian Hill
        leave_rh_time = daniel_start_time - travel_rh_to_richmond
        
        # We can't leave before we arrive
        if leave_rh_time < arrival_minutes:
            return False
        
        # Meeting must end before Daniel leaves
        meeting_end = daniel_start_time + min_meeting_duration
        if meeting_end > daniel_end_minutes:
            return False
        
        return True
    
    problem.addConstraint(travel_and_meeting_constraint, ['daniel_meeting_start'])
    
    # Find solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # No solution found that meets all constraints
        result = {"itinerary": []}
    else:
        # Use the first valid solution (all should be equivalent for our simple case)
        solution = solutions[0]
        daniel_meeting_start_minutes = solution['daniel_meeting_start']
        daniel_meeting_end_minutes = daniel_meeting_start_minutes + min_meeting_duration
        
        # Convert minutes back to time strings
        def minutes_to_time_str(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours}:{mins:02d}"
        
        leave_rh_time = daniel_meeting_start_minutes - travel_rh_to_richmond
        
        itinerary = [
            {
                "action": "travel", 
                "location": "Russian Hill to Richmond District", 
                "person": "Self", 
                "start_time": minutes_to_time_str(leave_rh_time), 
                "end_time": minutes_to_time_str(daniel_meeting_start_minutes)
            },
            {
                "action": "meet", 
                "location": "Richmond District", 
                "person": "Daniel", 
                "start_time": minutes_to_time_str(daniel_meeting_start_minutes), 
                "end_time": minutes_to_time_str(daniel_meeting_end_minutes)
            }
        ]
        
        result = {"itinerary": itinerary}
    
    # Output as JSON
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()