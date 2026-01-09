from constraint import Problem
import json

def main():
    # Define travel times in minutes
    travel_times = {
        ('Sunset District', 'Golden Gate Park'): 11,
        ('Golden Gate Park', 'Sunset District'): 10
    }
    
    # Convert times to minutes since midnight for easier calculation
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes
    
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"
    
    # Input parameters
    arrival_time = time_to_minutes("9:00")
    arrival_location = "Sunset District"
    
    joshua_start = time_to_minutes("20:45")  # 8:45 PM
    joshua_end = time_to_minutes("21:45")    # 9:45 PM
    joshua_location = "Golden Gate Park"
    min_meeting_time = 15
    
    # Create constraint problem
    problem = Problem()
    
    # Variables: start and end times for meeting Joshua
    # We need to determine when to travel to Golden Gate Park and meet Joshua
    problem.addVariable("depart_to_joshua", range(arrival_time, joshua_end - min_meeting_time + 1))
    problem.addVariable("meeting_duration", range(min_meeting_time, joshua_end - joshua_start + 1))
    
    # Constraints
    def meeting_constraints(depart_time, duration):
        travel_time = travel_times[(arrival_location, joshua_location)]
        
        # Arrival at Golden Gate Park
        arrival_at_park = depart_time + travel_time
        
        # Meeting must start after Joshua arrives and before he leaves
        meeting_start = max(arrival_at_park, joshua_start)
        meeting_end = meeting_start + duration
        
        # Meeting must end before Joshua leaves
        if meeting_end > joshua_end:
            return False
        
        # We must have enough time for the meeting
        if meeting_end - meeting_start < min_meeting_time:
            return False
            
        return True
    
    problem.addConstraint(meeting_constraints, ["depart_to_joshua", "meeting_duration"])
    
    # Find all solutions
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no meeting is possible, return empty itinerary
        result = {"itinerary": []}
        print(json.dumps(result, indent=2))
        return
    
    # Find optimal solution (maximize meeting duration)
    best_solution = max(solutions, key=lambda x: x["meeting_duration"])
    
    depart_time = best_solution["depart_to_joshua"]
    duration = best_solution["meeting_duration"]
    travel_time = travel_times[(arrival_location, joshua_location)]
    
    arrival_at_park = depart_time + travel_time
    meeting_start = max(arrival_at_park, joshua_start)
    meeting_end = meeting_start + duration
    
    # Build itinerary
    itinerary = []
    
    # Add travel to Golden Gate Park if we don't depart immediately
    if depart_time > arrival_time:
        itinerary.append({
            "action": "wait",
            "location": arrival_location,
            "person": None,
            "start_time": minutes_to_time(arrival_time),
            "end_time": minutes_to_time(depart_time)
        })
    
    # Add travel action
    itinerary.append({
        "action": "travel",
        "location": f"{arrival_location} to {joshua_location}",
        "person": None,
        "start_time": minutes_to_time(depart_time),
        "end_time": minutes_to_time(arrival_at_park)
    })
    
    # Add meeting with Joshua
    itinerary.append({
        "action": "meet",
        "location": joshua_location,
        "person": "Joshua",
        "start_time": minutes_to_time(meeting_start),
        "end_time": minutes_to_time(meeting_end)
    })
    
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()