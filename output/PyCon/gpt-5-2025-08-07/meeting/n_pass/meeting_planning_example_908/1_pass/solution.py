import constraint
from datetime import datetime, timedelta
import json

def main():
    # Define locations
    locations = [
        "Financial District", "Fisherman's Wharf", "Presidio", "Bayview", 
        "Haight-Ashbury", "Russian Hill", "The Castro", "Marina District", 
        "Richmond District", "Union Square", "Sunset District"
    ]
    
    # Travel time matrix (in minutes)
    travel_times = {
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Bayview"): 19,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Financial District", "Russian Hill"): 11,
        ("Financial District", "The Castro"): 20,
        ("Financial District", "Marina District"): 15,
        ("Financial District", "Richmond District"): 21,
        ("Financial District", "Union Square"): 9,
        ("Financial District", "Sunset District"): 30,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Bayview"): 26,
        ("Fisherman's Wharf", "Haight-Ashbury"): 22,
        ("Fisherman's Wharf", "Russian Hill"): 7,
        ("Fisherman's Wharf", "The Castro"): 27,
        ("Fisherman's Wharf", "Marina District"): 9,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Fisherman's Wharf", "Union Square"): 13,
        ("Fisherman's Wharf", "Sunset District"): 27,
        ("Presidio", "Financial District"): 23,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Bayview"): 31,
        ("Presidio", "Haight-Ashbury"): 15,
        ("Presidio", "Russian Hill"): 14,
        ("Presidio", "The Castro"): 21,
        ("Presidio", "Marina District"): 11,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Union Square"): 22,
        ("Presidio", "Sunset District"): 15,
        ("Bayview", "Financial District"): 19,
        ("Bayview", "Fisherman's Wharf"): 25,
        ("Bayview", "Presidio"): 32,
        ("Bayview", "Haight-Ashbury"): 19,
        ("Bayview", "Russian Hill"): 23,
        ("Bayview", "The Castro"): 19,
        ("Bayview", "Marina District"): 27,
        ("Bayview", "Richmond District"): 25,
        ("Bayview", "Union Square"): 18,
        ("Bayview", "Sunset District"): 23,
        ("Haight-Ashbury", "Financial District"): 21,
        ("Haight-Ashbury", "Fisherman's Wharf"): 23,
        ("Haight-Ashbury", "Presidio"): 15,
        ("Haight-Ashbury", "Bayview"): 18,
        ("Haight-Ashbury", "Russian Hill"): 17,
        ("Haight-Ashbury", "The Castro"): 6,
        ("Haight-Ashbury", "Marina District"): 17,
        ("Haight-Ashbury", "Richmond District"): 10,
        ("Haight-Ashbury", "Union Square"): 19,
        ("Haight-Ashbury", "Sunset District"): 15,
        ("Russian Hill", "Financial District"): 11,
        ("Russian Hill", "Fisherman's Wharf"): 7,
        ("Russian Hill", "Presidio"): 14,
        ("Russian Hill", "Bayview"): 23,
        ("Russian Hill", "Haight-Ashbury"): 17,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Union Square"): 10,
        ("Russian Hill", "Sunset District"): 23,
        ("The Castro", "Financial District"): 21,
        ("The Castro", "Fisherman's Wharf"): 24,
        ("The Castro", "Presidio"): 20,
        ("The Castro", "Bayview"): 19,
        ("The Castro", "Haight-Ashbury"): 6,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "Sunset District"): 17,
        ("Marina District", "Financial District"): 17,
        ("Marina District", "Fisherman's Wharf"): 10,
        ("Marina District", "Presidio"): 10,
        ("Marina District", "Bayview"): 27,
        ("Marina District", "Haight-Ashbury"): 16,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Sunset District"): 19,
        ("Richmond District", "Financial District"): 22,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Bayview"): 27,
        ("Richmond District", "Haight-Ashbury"): 10,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "Union Square"): 21,
        ("Richmond District", "Sunset District"): 11,
        ("Union Square", "Financial District"): 9,
        ("Union Square", "Fisherman's Wharf"): 15,
        ("Union Square", "Presidio"): 24,
        ("Union Square", "Bayview"): 15,
        ("Union Square", "Haight-Ashbury"): 18,
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "The Castro"): 17,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "Sunset District"): 27,
        ("Sunset District", "Financial District"): 30,
        ("Sunset District", "Fisherman's Wharf"): 29,
        ("Sunset District", "Presidio"): 16,
        ("Sunset District", "Bayview"): 22,
        ("Sunset District", "Haight-Ashbury"): 15,
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Union Square"): 30,
    }
    
    # Friend constraints
    friends = [
        {"name": "Mark", "location": "Fisherman's Wharf", "start": "8:15", "end": "10:00", "duration": 30},
        {"name": "Stephanie", "location": "Presidio", "start": "12:15", "end": "15:00", "duration": 75},
        {"name": "Betty", "location": "Bayview", "start": "7:15", "end": "20:30", "duration": 15},
        {"name": "Lisa", "location": "Haight-Ashbury", "start": "15:30", "end": "18:30", "duration": 45},
        {"name": "William", "location": "Russian Hill", "start": "18:45", "end": "20:00", "duration": 60},
        {"name": "Brian", "location": "The Castro", "start": "9:15", "end": "13:15", "duration": 30},
        {"name": "Joseph", "location": "Marina District", "start": "10:45", "end": "15:00", "duration": 90},
        {"name": "Ashley", "location": "Richmond District", "start": "9:45", "end": "11:15", "duration": 45},
        {"name": "Patricia", "location": "Union Square", "start": "16:30", "end": "20:00", "duration": 120},
        {"name": "Karen", "location": "Sunset District", "start": "16:30", "end": "22:00", "duration": 105}
    ]
    
    # Convert time strings to minutes since 9:00
    def time_to_minutes(time_str):
        time_obj = datetime.strptime(time_str, "%H:%M")
        base_time = datetime.strptime("9:00", "%H:%M")
        return int((time_obj - base_time).total_seconds() / 60)
    
    # Convert minutes to time string
    def minutes_to_time(minutes):
        base_time = datetime.strptime("9:00", "%H:%M")
        result_time = base_time + timedelta(minutes=minutes)
        return result_time.strftime("%H:%M").lstrip("0")
    
    # Convert all times to minutes since 9:00
    for friend in friends:
        friend["start_min"] = time_to_minutes(friend["start"])
        friend["end_min"] = time_to_minutes(friend["end"])
    
    # Create problem
    problem = constraint.Problem()
    
    # Variables: start time for each meeting (in minutes since 9:00)
    for friend in friends:
        # Meeting must start within friend's availability window minus duration
        earliest_start = friend["start_min"]
        latest_start = friend["end_min"] - friend["duration"]
        if latest_start >= earliest_start:
            problem.addVariable(friend["name"], range(earliest_start, latest_start + 1))
    
    # Function to check if two meetings can be scheduled with travel time
    def can_schedule_meetings(meeting1_name, meeting2_name):
        friend1 = next(f for f in friends if f["name"] == meeting1_name)
        friend2 = next(f for f in friends if f["name"] == meeting2_name)
        
        start1 = friend1["start_min"]
        end1 = friend1["end_min"]
        duration1 = friend1["duration"]
        location1 = friend1["location"]
        
        start2 = friend2["start_min"]
        end2 = friend2["end_min"]
        duration2 = friend2["duration"]
        location2 = friend2["location"]
        
        travel_time = travel_times.get((location1, location2), 60)  # Default to 60 if not found
        
        # Check if meetings overlap in time considering travel
        def constraint_func(time1, time2):
            # Meeting 1 ends at time1 + duration1
            # Meeting 2 starts at time2
            # We need time1 + duration1 + travel_time <= time2
            # OR time2 + duration2 + travel_time <= time1
            return (time1 + duration1 + travel_time <= time2) or (time2 + duration2 + travel_time <= time1)
        
        return constraint_func
    
    # Add constraints for all pairs of meetings
    for i in range(len(friends)):
        for j in range(i + 1, len(friends)):
            friend1 = friends[i]
            friend2 = friends[j]
            
            # Only add constraint if both friends have valid time windows
            if (friend1["end_min"] - friend1["duration"] >= friend1["start_min"] and
                friend2["end_min"] - friend2["duration"] >= friend2["start_min"]):
                constraint_func = can_schedule_meetings(friend1["name"], friend2["name"])
                problem.addConstraint(constraint_func, [friend1["name"], friend2["name"]])
    
    # Find a solution
    solution = problem.getSolution()
    
    # If no solution found, try to find a partial solution
    if not solution:
        # Sort friends by priority (earlier availability first)
        available_friends = [f for f in friends if f["end_min"] - f["duration"] >= f["start_min"]]
        available_friends.sort(key=lambda x: x["start_min"])
        
        solution = {}
        current_time = 0  # Start at 9:00
        current_location = "Financial District"
        
        for friend in available_friends:
            # Calculate travel time to this friend
            travel_time = travel_times.get((current_location, friend["location"]), 60)
            
            # Earliest we can start meeting with this friend
            earliest_start = max(current_time + travel_time, friend["start_min"])
            
            # Check if we can fit the meeting
            if earliest_start + friend["duration"] <= friend["end_min"]:
                solution[friend["name"]] = earliest_start
                current_time = earliest_start + friend["duration"]
                current_location = friend["location"]
    
    # Build itinerary
    itinerary = []
    
    if solution:
        # Create list of meetings with their times
        meetings = []
        for friend_name, start_time in solution.items():
            friend = next(f for f in friends if f["name"] == friend_name)
            meetings.append({
                "name": friend_name,
                "location": friend["location"],
                "start": start_time,
                "end": start_time + friend["duration"],
                "duration": friend["duration"]
            })
        
        # Sort meetings by start time
        meetings.sort(key=lambda x: x["start"])
        
        # Add travel from Financial District to first meeting
        if meetings:
            first_meeting = meetings[0]
            travel_time = travel_times.get(("Financial District", first_meeting["location"]), 60)
            if first_meeting["start"] > travel_time:
                itinerary.append({
                    "action": "travel",
                    "location": first_meeting["location"],
                    "person": "",
                    "start_time": minutes_to_time(0),
                    "end_time": minutes_to_time(first_meeting["start"])
                })
        
        # Add meetings
        for i, meeting in enumerate(meetings):
            itinerary.append({
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["name"],
                "start_time": minutes_to_time(meeting["start"]),
                "end_time": minutes_to_time(meeting["end"])
            })
            
            # Add travel to next meeting if there is one
            if i < len(meetings) - 1:
                next_meeting = meetings[i + 1]
                travel_time = travel_times.get((meeting["location"], next_meeting["location"]), 60)
                
                # Only add travel if there's a gap
                if meeting["end"] + travel_time < next_meeting["start"]:
                    itinerary.append({
                        "action": "travel",
                        "location": next_meeting["location"],
                        "person": "",
                        "start_time": minutes_to_time(meeting["end"]),
                        "end_time": minutes_to_time(next_meeting["start"])
                    })
    
    # Output result
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()