from z3 import *
import json

def solve_scheduling_problem():
    # Initialize Z3 solver
    s = Solver()

    # Define the friends and their availability
    friends = {
        "Jessica": {"location": "Golden Gate Park", "start": (13, 45), "end": (15, 0), "min_duration": 30},
        "Ashley": {"location": "Bayview", "start": (17, 15), "end": (20, 0), "min_duration": 105},
        "Ronald": {"location": "Chinatown", "start": (7, 15), "end": (14, 45), "min_duration": 90},
        "William": {"location": "North Beach", "start": (13, 15), "end": (20, 15), "min_duration": 15},
        "Daniel": {"location": "Mission District", "start": (7, 0), "end": (11, 15), "min_duration": 105}
    }

    # Define travel times (in minutes) between locations
    travel_times = {
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "Chinatown"): 21,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Mission District"): 26,
        ("Golden Gate Park", "Presidio"): 11,
        ("Golden Gate Park", "Bayview"): 23,
        ("Golden Gate Park", "Chinatown"): 23,
        ("Golden Gate Park", "North Beach"): 24,
        ("Golden Gate Park", "Mission District"): 17,
        ("Bayview", "Presidio"): 31,
        ("Bayview", "Golden Gate Park"): 22,
        ("Bayview", "Chinatown"): 18,
        ("Bayview", "North Beach"): 21,
        ("Bayview", "Mission District"): 13,
        ("Chinatown", "Presidio"): 19,
        ("Chinatown", "Golden Gate Park"): 23,
        ("Chinatown", "Bayview"): 22,
        ("Chinatown", "North Beach"): 3,
        ("Chinatown", "Mission District"): 18,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Bayview"): 22,
        ("North Beach", "Chinatown"): 6,
        ("North Beach", "Mission District"): 18,
        ("Mission District", "Presidio"): 25,
        ("Mission District", "Golden Gate Park"): 17,
        ("Mission District", "Bayview"): 15,
        ("Mission District", "Chinatown"): 16,
        ("Mission District", "North Beach"): 17
    }

    # Current location starts at Presidio at 9:00 AM
    current_time_min = 9 * 60  # 9:00 AM in minutes
    current_location = "Presidio"

    # Convert all times to minutes since midnight for easier arithmetic
    def to_minutes(time):
        return time[0] * 60 + time[1]

    def from_minutes(minutes):
        return (minutes // 60, minutes % 60)

    # Variables to track meetings
    meetings = []
    for name, info in friends.items():
        start_min = to_minutes(info["start"])
        end_min = to_minutes(info["end"])
        min_duration = info["min_duration"]

        meet_start = Int(f"meet_start_{name}")
        meet_end = Int(f"meet_end_{name}")

        # Add constraints for meeting within friend's availability
        s.add(meet_start >= start_min)
        s.add(meet_end <= end_min)
        s.add(meet_end - meet_start >= min_duration)

        meetings.append({
            "name": name,
            "location": info["location"],
            "start": meet_start,
            "end": meet_end
        })

    # Create a meeting order variable to determine sequence
    meeting_order = [Int(f"order_{i}") for i in range(len(meetings))]
    s.add(Distinct(meeting_order))
    for i in range(len(meetings)):
        s.add(meeting_order[i] >= 0)
        s.add(meeting_order[i] < len(meetings))

    # Function to get travel time between two locations
    def get_travel_time(from_loc, to_loc):
        return travel_times.get((from_loc, to_loc), 0)

    # Add sequencing constraints with travel times
    for i in range(len(meetings)):
        for j in range(len(meetings)):
            if i != j:
                # If meeting i comes before meeting j
                i_before_j = meeting_order[i] < meeting_order[j]
                travel_time = get_travel_time(meetings[i]["location"], meetings[j]["location"])
                s.add(Implies(i_before_j, meetings[j]["start"] >= meetings[i]["end"] + travel_time))

    # Add initial travel time constraint
    first_meeting = [m for m in meetings if meeting_order[meetings.index(m)] == 0][0]
    initial_travel_time = get_travel_time(current_location, first_meeting["location"])
    s.add(first_meeting["start"] >= current_time_min + initial_travel_time)

    # Try to find a solution
    if s.check() == sat:
        model = s.model()
        # Get the meeting order from the model
        ordered_meetings = sorted(meetings, key=lambda m: model.eval(meeting_order[meetings.index(m)]).as_long())
        
        itinerary = []
        current_time = current_time_min
        current_loc = current_location
        
        for meet in ordered_meetings:
            start = model.eval(meet["start"]).as_long()
            end = model.eval(meet["end"]).as_long()
            
            # Calculate travel time
            travel_time = get_travel_time(current_loc, meet["location"])
            arrival_time = current_time + travel_time
            
            # Ensure we arrive before the meeting starts
            s.add(arrival_time <= start)
            
            start_time = from_minutes(start)
            end_time = from_minutes(end)
            itinerary.append({
                "action": "meet",
                "person": meet["name"],
                "start_time": f"{start_time[0]:02d}:{start_time[1]:02d}",
                "end_time": f"{end_time[0]:02d}:{end_time[1]:02d}"
            })
            
            current_time = end
            current_loc = meet["location"]
        
        return {"itinerary": itinerary}
    else:
        # Try with subsets if full schedule isn't possible
        for subset_size in range(len(meetings), 0, -1):
            for subset in permutations(meetings, subset_size):
                temp_solver = Solver()
                # Copy constraints for this subset
                for meet in subset:
                    temp_solver.add(meet["start"] >= to_minutes(friends[meet["name"]]["start"]))
                    temp_solver.add(meet["end"] <= to_minutes(friends[meet["name"]]["end"]))
                    temp_solver.add(meet["end"] - meet["start"] >= friends[meet["name"]]["min_duration"])
                
                # Add initial travel time constraint
                first_subset_meeting = subset[0]
                initial_travel_time = get_travel_time(current_location, first_subset_meeting["location"])
                temp_solver.add(first_subset_meeting["start"] >= current_time_min + initial_travel_time)
                
                # Add sequencing constraints
                for i in range(len(subset)):
                    for j in range(len(subset)):
                        if i != j:
                            i_before_j = Int(f"order_{i}_{j}")
                            temp_solver.add(Or(i_before_j == 0, i_before_j == 1))
                            travel_time = get_travel_time(subset[i]["location"], subset[j]["location"])
                            temp_solver.add(Implies(i_before_j == 1, subset[j]["start"] >= subset[i]["end"] + travel_time))
                
                if temp_solver.check() == sat:
                    model = temp_solver.model()
                    ordered_subset = sorted(subset, key=lambda m: model.eval(Int(f"order_{subset.index(m)}_{subset.index(m)}")).as_long() if len(subset) > 1 else [m for m in subset])
                    
                    itinerary = []
                    current_time = current_time_min
                    current_loc = current_location
                    
                    for meet in ordered_subset:
                        start = model.eval(meet["start"]).as_long()
                        end = model.eval(meet["end"]).as_long()
                        
                        travel_time = get_travel_time(current_loc, meet["location"])
                        arrival_time = current_time + travel_time
                        
                        start_time = from_minutes(start)
                        end_time = from_minutes(end)
                        itinerary.append({
                            "action": "meet",
                            "person": meet["name"],
                            "start_time": f"{start_time[0]:02d}:{start_time[1]:02d}",
                            "end_time": f"{end_time[0]:02d}:{end_time[1]:02d}"
                        })
                        
                        current_time = end
                        current_loc = meet["location"]
                    
                    return {"itinerary": itinerary}
        
        return {"itinerary": []}

solution = solve_scheduling_problem()
print("SOLUTION:")
print(json.dumps(solution, indent=2))