import constraint
import json
from datetime import datetime, timedelta

def main():
    # Input parameters
    start_location = "Alamo Square"
    start_time = datetime.strptime("9:00", "%H:%M")
    
    # Travel times in minutes
    travel_times = {
        ("Alamo Square", "Richmond District"): 12,
        ("Richmond District", "Alamo Square"): 13
    }
    
    # Timothy's availability
    timothy_start = datetime.strptime("20:45", "%H:%M")  # 8:45 PM
    timothy_end = datetime.strptime("21:30", "%H:%M")    # 9:30 PM
    min_meeting_duration = 45  # minutes
    
    # Create problem instance
    problem = constraint.Problem()
    
    # Define variables: meeting start time (in minutes from 9:00 AM)
    max_time_minutes = 24 * 60  # Full day in minutes
    
    # Add variable for meeting start time with Timothy
    problem.addVariable("meeting_start", range(max_time_minutes))
    
    # Constraints for Timothy meeting
    def timothy_constraint(meeting_start_minutes):
        meeting_start = start_time + timedelta(minutes=meeting_start_minutes)
        meeting_end = meeting_start + timedelta(minutes=min_meeting_duration)
        
        # Must meet during Timothy's availability
        if meeting_start < timothy_start or meeting_end > timothy_end:
            return False
        
        # Calculate travel time to Richmond District
        travel_to_richmond = travel_times[("Alamo Square", "Richmond District")]
        
        # Must have enough time to travel to Richmond District
        arrival_time = start_time + timedelta(minutes=travel_to_richmond)
        if meeting_start < arrival_time:
            return False
        
        return True
    
    problem.addConstraint(timothy_constraint, ["meeting_start"])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if solutions:
        # Get the first valid solution
        solution = solutions[0]
        meeting_start_minutes = solution["meeting_start"]
        meeting_start_time = start_time + timedelta(minutes=meeting_start_minutes)
        meeting_end_time = meeting_start_time + timedelta(minutes=min_meeting_duration)
        
        # Format times for output
        def format_time(dt):
            return dt.strftime("%H:%M")
        
        itinerary = [
            {
                "action": "travel",
                "location": "Richmond District", 
                "person": "Self",
                "start_time": format_time(start_time),
                "end_time": format_time(start_time + timedelta(minutes=travel_times[("Alamo Square", "Richmond District")]))
            },
            {
                "action": "meet",
                "location": "Richmond District",
                "person": "Timothy", 
                "start_time": format_time(meeting_start_time),
                "end_time": format_time(meeting_end_time)
            }
        ]
        
        result = {
            "itinerary": itinerary
        }
        
        print(json.dumps(result, indent=2))
    else:
        # No valid solution found
        print(json.dumps({"itinerary": []}, indent=2))

if __name__ == "__main__":
    main()