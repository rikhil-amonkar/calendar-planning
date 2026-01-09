import constraint
from datetime import datetime, timedelta
import json

def main():
    # Define locations
    locations = ["Golden Gate Park", "Haight-Ashbury", "Sunset District", "Marina District", "Financial District", "Union Square"]
    
    # Travel times matrix (in minutes)
    travel_times = {
        "Golden Gate Park": {"Golden Gate Park": 0, "Haight-Ashbury": 7, "Sunset District": 10, "Marina District": 16, "Financial District": 26, "Union Square": 22},
        "Haight-Ashbury": {"Golden Gate Park": 7, "Haight-Ashbury": 0, "Sunset District": 15, "Marina District": 17, "Financial District": 21, "Union Square": 17},
        "Sunset District": {"Golden Gate Park": 11, "Haight-Ashbury": 15, "Sunset District": 0, "Marina District": 21, "Financial District": 30, "Union Square": 30},
        "Marina District": {"Golden Gate Park": 18, "Haight-Ashbury": 16, "Sunset District": 19, "Marina District": 0, "Financial District": 17, "Union Square": 16},
        "Financial District": {"Golden Gate Park": 23, "Haight-Ashbury": 19, "Sunset District": 31, "Marina District": 15, "Financial District": 0, "Union Square": 9},
        "Union Square": {"Golden Gate Park": 22, "Haight-Ashbury": 18, "Sunset District": 26, "Marina District": 18, "Financial District": 9, "Union Square": 0}
    }
    
    # Friend constraints
    friends = {
        "Sarah": {
            "location": "Haight-Ashbury",
            "available_start": datetime.strptime("17:00", "%H:%M"),
            "available_end": datetime.strptime("21:30", "%H:%M"),
            "min_duration": 105
        },
        "Patricia": {
            "location": "Sunset District",
            "available_start": datetime.strptime("17:00", "%H:%M"),
            "available_end": datetime.strptime("19:45", "%H:%M"),
            "min_duration": 45
        },
        "Matthew": {
            "location": "Marina District",
            "available_start": datetime.strptime("9:15", "%H:%M"),
            "available_end": datetime.strptime("12:00", "%H:%M"),
            "min_duration": 15
        },
        "Joseph": {
            "location": "Financial District",
            "available_start": datetime.strptime("14:15", "%H:%M"),
            "available_end": datetime.strptime("18:45", "%H:%M"),
            "min_duration": 30
        },
        "Robert": {
            "location": "Union Square",
            "available_start": datetime.strptime("10:15", "%H:%M"),
            "available_end": datetime.strptime("21:45", "%H:%M"),
            "min_duration": 15
        }
    }
    
    # Start at Golden Gate Park at 9:00 AM
    current_time = datetime.strptime("9:00", "%H:%M")
    current_location = "Golden Gate Park"
    
    problem = constraint.Problem()
    
    # Define variables for each friend: start_time (minutes from 9:00), duration (minutes)
    friend_vars = {}
    for friend in friends:
        friend_vars[friend] = {
            "start": friend + "_start",
            "duration": friend + "_duration"
        }
        # Start time in minutes from 9:00 (0 = 9:00)
        available_start_min = int((friends[friend]["available_start"] - current_time).total_seconds() / 60)
        available_end_min = int((friends[friend]["available_end"] - current_time).total_seconds() / 60)
        min_duration = friends[friend]["min_duration"]
        
        problem.addVariable(friend + "_start", range(available_start_min, available_end_min - min_duration + 1))
        problem.addVariable(friend + "_duration", range(min_duration, available_end_min - available_start_min + 1))
    
    # Add constraint that meetings cannot overlap and must account for travel
    def no_overlap(*args):
        # Extract start times and durations for all friends
        values = {}
        for i, friend in enumerate(friends):
            values[friend] = {
                "start": args[i * 2],
                "duration": args[i * 2 + 1],
                "location": friends[friend]["location"]
            }
        
        # Sort by start time
        sorted_friends = sorted(values.keys(), key=lambda f: values[f]["start"])
        
        # Check for overlaps considering travel time
        for i in range(len(sorted_friends) - 1):
            friend1 = sorted_friends[i]
            friend2 = sorted_friends[i + 1]
            
            end_time_friend1 = values[friend1]["start"] + values[friend1]["duration"]
            travel_time = travel_times[values[friend1]["location"]][values[friend2]["location"]]
            
            if end_time_friend1 + travel_time > values[friend2]["start"]:
                return False
        
        return True
    
    # Add the constraint
    all_vars = []
    for friend in friends:
        all_vars.append(friend_vars[friend]["start"])
        all_vars.append(friend_vars[friend]["duration"])
    
    problem.addConstraint(no_overlap, all_vars)
    
    # Objective: maximize total meeting time
    def objective(*args):
        total_duration = 0
        for i in range(len(friends)):
            total_duration += args[i * 2 + 1]  # duration is at odd indices
        return total_duration
    
    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to meet as many friends as possible with minimum durations
        best_solution = None
        best_score = -1
        
        for friend in friends:
            # Try meeting just this one friend
            single_friend_problem = constraint.Problem()
            single_friend_problem.addVariable(friend + "_start", 
                range(int((friends[friend]["available_start"] - current_time).total_seconds() / 60),
                      int((friends[friend]["available_end"] - current_time).total_seconds() / 60) - friends[friend]["min_duration"] + 1))
            single_friend_problem.addVariable(friend + "_duration", [friends[friend]["min_duration"]])
            
            single_solutions = single_friend_problem.getSolutions()
            if single_solutions:
                if best_score < 1:
                    best_solution = single_solutions[0]
                    best_score = 1
        
        if best_solution:
            solution = best_solution
        else:
            solution = {}
    else:
        # Find solution with maximum total duration
        solution = max(solutions, key=lambda s: sum(s[friend_vars[friend]["duration"]] for friend in friends))
    
    # Build itinerary
    itinerary = []
    
    # Add meetings to itinerary
    meetings = []
    for friend in friends:
        if friend_vars[friend]["start"] in solution:
            start_minutes = solution[friend_vars[friend]["start"]]
            duration = solution[friend_vars[friend]["duration"]]
            
            start_time = current_time + timedelta(minutes=start_minutes)
            end_time = start_time + timedelta(minutes=duration)
            
            meetings.append({
                "friend": friend,
                "location": friends[friend]["location"],
                "start": start_time,
                "end": end_time
            })
    
    # Sort meetings by start time
    meetings.sort(key=lambda x: x["start"])
    
    # Add travel from starting location to first meeting
    if meetings:
        first_meeting = meetings[0]
        travel_start = current_time
        travel_end = current_time + timedelta(minutes=travel_times[current_location][first_meeting["location"]])
        
        if travel_end < first_meeting["start"]:
            itinerary.append({
                "action": "travel",
                "location": first_meeting["location"],
                "person": "",
                "start_time": travel_start.strftime("%H:%M"),
                "end_time": travel_end.strftime("%H:%M")
            })
    
    # Add meetings and travel between them
    for i, meeting in enumerate(meetings):
        # Add the meeting
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["friend"],
            "start_time": meeting["start"].strftime("%H:%M"),
            "end_time": meeting["end"].strftime("%H:%M")
        })
        
        # Add travel to next meeting if there is one
        if i < len(meetings) - 1:
            next_meeting = meetings[i + 1]
            travel_time_needed = travel_times[meeting["location"]][next_meeting["location"]]
            
            travel_start = meeting["end"]
            travel_end = travel_start + timedelta(minutes=travel_time_needed)
            
            if travel_end < next_meeting["start"]:
                # We have time to travel directly
                itinerary.append({
                    "action": "travel",
                    "location": next_meeting["location"],
                    "person": "",
                    "start_time": travel_start.strftime("%H:%M"),
                    "end_time": travel_end.strftime("%H:%M")
                })
            else:
                # Need to account for waiting time or adjust schedule
                pass
    
    # Output as JSON
    output = {
        "itinerary": itinerary
    }
    
    print(json.dumps(output, indent=2))

if __name__ == "__main__":
    main()