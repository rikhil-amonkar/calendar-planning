import constraint
from datetime import datetime, timedelta
import json

def main():
    # Define all locations
    locations = [
        "Marina District", "Richmond District", "Union Square", "Nob Hill",
        "Fisherman's Wharf", "Golden Gate Park", "Embarcadero", "Financial District",
        "North Beach", "Presidio"
    ]
    
    # Create travel time dictionary
    travel_times = {
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Nob Hill"): 12,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Golden Gate Park"): 18,
        ("Marina District", "Embarcadero"): 14,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Presidio"): 10,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Union Square"): 21,
        ("Richmond District", "Nob Hill"): 17,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Richmond District", "Embarcadero"): 19,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Presidio"): 7,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "Nob Hill"): 9,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Golden Gate Park"): 22,
        ("Union Square", "Embarcadero"): 11,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Presidio"): 24,
        ("Nob Hill", "Marina District"): 11,
        ("Nob Hill", "Richmond District"): 14,
        ("Nob Hill", "Union Square"): 7,
        ("Nob Hill", "Fisherman's Wharf"): 10,
        ("Nob Hill", "Golden Gate Park"): 17,
        ("Nob Hill", "Embarcadero"): 9,
        ("Nob Hill", "Financial District"): 9,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Presidio"): 17,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Golden Gate Park"): 25,
        ("Fisherman's Wharf", "Embarcadero"): 8,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Union Square"): 22,
        ("Golden Gate Park", "Nob Hill"): 20,
        ("Golden Gate Park", "Fisherman's Wharf"): 24,
        ("Golden Gate Park", "Embarcadero"): 25,
        ("Golden Gate Park", "Financial District"): 26,
        ("Golden Gate Park", "North Beach"): 23,
        ("Golden Gate Park", "Presidio"): 11,
        ("Embarcadero", "Marina District"): 12,
        ("Embarcadero", "Richmond District"): 21,
        ("Embarcadero", "Union Square"): 10,
        ("Embarcadero", "Nob Hill"): 10,
        ("Embarcadero", "Fisherman's Wharf"): 6,
        ("Embarcadero", "Golden Gate Park"): 25,
        ("Embarcadero", "Financial District"): 5,
        ("Embarcadero", "North Beach"): 5,
        ("Embarcadero", "Presidio"): 20,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Nob Hill"): 8,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Golden Gate Park"): 23,
        ("Financial District", "Embarcadero"): 4,
        ("Financial District", "North Beach"): 7,
        ("Financial District", "Presidio"): 22,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Golden Gate Park"): 22,
        ("North Beach", "Embarcadero"): 6,
        ("North Beach", "Financial District"): 8,
        ("North Beach", "Presidio"): 17,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Golden Gate Park"): 12,
        ("Presidio", "Embarcadero"): 20,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "North Beach"): 18
    }
    
    # Friend constraints
    friends = {
        "Stephanie": {
            "location": "Richmond District",
            "available_start": datetime.strptime("16:15", "%H:%M"),
            "available_end": datetime.strptime("21:30", "%H:%M"),
            "min_duration": 75
        },
        "William": {
            "location": "Union Square",
            "available_start": datetime.strptime("10:45", "%H:%M"),
            "available_end": datetime.strptime("17:30", "%H:%M"),
            "min_duration": 45
        },
        "Elizabeth": {
            "location": "Nob Hill",
            "available_start": datetime.strptime("12:15", "%H:%M"),
            "available_end": datetime.strptime("15:00", "%H:%M"),
            "min_duration": 105
        },
        "Joseph": {
            "location": "Fisherman's Wharf",
            "available_start": datetime.strptime("12:45", "%H:%M"),
            "available_end": datetime.strptime("14:00", "%H:%M"),
            "min_duration": 75
        },
        "Anthony": {
            "location": "Golden Gate Park",
            "available_start": datetime.strptime("13:00", "%H:%M"),
            "available_end": datetime.strptime("20:30", "%H:%M"),
            "min_duration": 75
        },
        "Barbara": {
            "location": "Embarcadero",
            "available_start": datetime.strptime("19:15", "%H:%M"),
            "available_end": datetime.strptime("20:30", "%H:%M"),
            "min_duration": 75
        },
        "Carol": {
            "location": "Financial District",
            "available_start": datetime.strptime("11:45", "%H:%M"),
            "available_end": datetime.strptime("16:15", "%H:%M"),
            "min_duration": 60
        },
        "Sandra": {
            "location": "North Beach",
            "available_start": datetime.strptime("10:00", "%H:%M"),
            "available_end": datetime.strptime("12:30", "%H:%M"),
            "min_duration": 15
        },
        "Kenneth": {
            "location": "Presidio",
            "available_start": datetime.strptime("21:15", "%H:%M"),
            "available_end": datetime.strptime("22:15", "%H:%M"),
            "min_duration": 45
        }
    }
    
    # Convert times to minutes since 9:00
    def time_to_minutes(time_str):
        dt = datetime.strptime(time_str, "%H:%M")
        start_time = datetime.strptime("9:00", "%H:%M")
        delta = dt - start_time
        return int(delta.total_seconds() / 60)
    
    # Convert minutes to time string
    def minutes_to_time(minutes):
        start_time = datetime.strptime("9:00", "%H:%M")
        new_time = start_time + timedelta(minutes=minutes)
        return new_time.strftime("%H:%M").lstrip('0')
    
    # Create problem
    problem = constraint.Problem()
    
    # Define variables for each friend: start_time, duration
    for friend in friends:
        available_start_min = time_to_minutes(friends[friend]["available_start"].strftime("%H:%M"))
        available_end_min = time_to_minutes(friends[friend]["available_end"].strftime("%H:%M"))
        min_duration = friends[friend]["min_duration"]
        
        # Start time must be within availability window
        problem.addVariable(f"{friend}_start", range(available_start_min, available_end_min - min_duration + 1))
        # Duration must be at least the minimum
        problem.addVariable(f"{friend}_duration", range(min_duration, available_end_min - available_start_min + 1))
    
    # Add constraints for travel time between consecutive meetings
    friend_names = list(friends.keys())
    
    for i in range(len(friend_names)):
        for j in range(i + 1, len(friend_names)):
            friend1 = friend_names[i]
            friend2 = friend_names[j]
            
            loc1 = friends[friend1]["location"]
            loc2 = friends[friend2]["location"]
            
            travel_time = travel_times.get((loc1, loc2), travel_times.get((loc2, loc1), 0))
            
            # If friend1 meets before friend2
            def travel_constraint_before(start1, dur1, start2, dur2):
                return start1 + dur1 + travel_time <= start2
            
            # If friend2 meets before friend1  
            def travel_constraint_after(start2, dur2, start1, dur1):
                return start2 + dur2 + travel_time <= start1
            
            problem.addConstraint(
                travel_constraint_before,
                [f"{friend1}_start", f"{friend1}_duration", f"{friend2}_start", f"{friend2}_duration"]
            )
            problem.addConstraint(
                travel_constraint_after,
                [f"{friend2}_start", f"{friend2}_duration", f"{friend1}_start", f"{friend1}_duration"]
            )
    
    # Objective: maximize total meeting time
    def objective_function(*args):
        total_duration = 0
        # Sum all durations
        for i in range(len(friend_names)):
            total_duration += args[i * 2 + 1]  # duration is at odd indices
        return total_duration
    
    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to meet as many friends as possible with minimum durations
        best_solution = None
        max_meetings = 0
        
        # Try different orders
        from itertools import permutations
        
        for order in permutations(friend_names):
            current_time = 0  # Start at 9:00
            itinerary = []
            
            for friend in order:
                friend_info = friends[friend]
                available_start = time_to_minutes(friend_info["available_start"].strftime("%H:%M"))
                available_end = time_to_minutes(friend_info["available_end"].strftime("%H:%M"))
                min_duration = friend_info["min_duration"]
                
                # Calculate earliest possible start time
                if itinerary:
                    last_location = itinerary[-1]["location"]
                    current_location = friend_info["location"]
                    travel_time = travel_times.get((last_location, current_location), 30)
                    earliest_start = current_time + travel_time
                else:
                    earliest_start = current_time
                
                # Adjust start time to be within availability
                start_time = max(earliest_start, available_start)
                
                # Check if we can meet for minimum duration
                if start_time + min_duration <= available_end:
                    end_time = start_time + min_duration
                    itinerary.append({
                        "action": "meet",
                        "location": friend_info["location"],
                        "person": friend,
                        "start_time": minutes_to_time(start_time),
                        "end_time": minutes_to_time(end_time)
                    })
                    current_time = end_time
            
            if len(itinerary) > max_meetings:
                max_meetings = len(itinerary)
                best_solution = itinerary
        
        result = {"itinerary": best_solution if best_solution else []}
    else:
        # Find solution with maximum total duration
        best_solution = max(solutions, key=lambda sol: sum(sol[f"{friend}_duration"] for friend in friend_names))
        
        # Create itinerary from solution
        itinerary = []
        meeting_times = []
        
        for friend in friend_names:
            start_time = best_solution[f"{friend}_start"]
            duration = best_solution[f"{friend}_duration"]
            end_time = start_time + duration
            
            meeting_times.append({
                "friend": friend,
                "start": start_time,
                "end": end_time,
                "location": friends[friend]["location"]
            })
        
        # Sort by start time
        meeting_times.sort(key=lambda x: x["start"])
        
        for meeting in meeting_times:
            itinerary.append({
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["friend"],
                "start_time": minutes_to_time(meeting["start"]),
                "end_time": minutes_to_time(meeting["end"])
            })
        
        result = {"itinerary": itinerary}
    
    # Output as JSON
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()