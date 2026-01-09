import constraint
from datetime import datetime, timedelta
import json

def main():
    # Input parameters
    start_location = "Fisherman's Wharf"
    start_time = datetime.strptime("9:00", "%H:%M")
    
    # Travel times in minutes
    travel_times = {
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Nob Hill", "Fisherman's Wharf"): 11
    }
    
    # Kenneth's availability
    kenneth_available_start = datetime.strptime("14:15", "%H:%M")
    kenneth_available_end = datetime.strptime("19:45", "%H:%M")
    kenneth_min_duration = 90  # minutes
    
    # Create problem instance
    problem = constraint.Problem()
    
    # Convert all times to minutes since start for easier computation
    start_minutes = 0  # 9:00 AM = 0 minutes
    kenneth_start_minutes = (kenneth_available_start - start_time).total_seconds() / 60
    kenneth_end_minutes = (kenneth_available_end - start_time).total_seconds() / 60
    
    # Variables: meeting start time with Kenneth (in minutes from start)
    problem.addVariable("kenneth_meet_start", range(int(kenneth_start_minutes), int(kenneth_end_minutes - kenneth_min_duration) + 1))
    
    # Constraints: meeting must fit within Kenneth's availability and account for travel
    def meeting_constraint(k_start):
        # Calculate meeting end time
        k_end = k_start + kenneth_min_duration
        
        # Check if meeting fits within Kenneth's availability
        if k_end > kenneth_end_minutes:
            return False
            
        # Check travel feasibility - we need to arrive at Nob Hill by k_start
        # We start at Fisherman's Wharf at time 0
        travel_to_nob_hill = travel_times[("Fisherman's Wharf", "Nob Hill")]
        
        # We can leave Fisherman's Wharf at: k_start - travel_to_nob_hill
        departure_time = k_start - travel_to_nob_hill
        
        # We must have enough time to travel there
        if departure_time < 0:
            return False
            
        return True
    
    problem.addConstraint(meeting_constraint, ["kenneth_meet_start"])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        # If no solution found, create empty itinerary
        result = {"itinerary": []}
    else:
        # Use the first valid solution
        solution = solutions[0]
        k_start_minutes = solution["kenneth_meet_start"]
        k_end_minutes = k_start_minutes + kenneth_min_duration
        
        # Convert back to datetime objects
        k_start_time = start_time + timedelta(minutes=k_start_minutes)
        k_end_time = start_time + timedelta(minutes=k_end_minutes)
        
        # Calculate travel times
        travel_to_nob_hill = travel_times[("Fisherman's Wharf", "Nob Hill")]
        departure_time = k_start_time - timedelta(minutes=travel_to_nob_hill)
        
        # Build itinerary
        itinerary = []
        
        # Add travel to Nob Hill
        itinerary.append({
            "action": "travel",
            "location": "Nob Hill",
            "person": "Self",
            "start_time": departure_time.strftime("%H:%M"),
            "end_time": k_start_time.strftime("%H:%M")
        })
        
        # Add meeting with Kenneth
        itinerary.append({
            "action": "meet",
            "location": "Nob Hill",
            "person": "Kenneth",
            "start_time": k_start_time.strftime("%H:%M"),
            "end_time": k_end_time.strftime("%H:%M")
        })
        
        result = {"itinerary": itinerary}
    
    # Output as JSON
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()