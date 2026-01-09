import constraint
from datetime import datetime, timedelta
import json

def main():
    # Define locations
    locations = [
        "Chinatown", "Embarcadero", "Pacific Heights", "Russian Hill", 
        "Haight-Ashbury", "Golden Gate Park", "Fisherman's Wharf", 
        "Sunset District", "The Castro"
    ]
    
    # Travel time matrix (in minutes)
    travel_times = {
        "Chinatown": {
            "Chinatown": 0, "Embarcadero": 5, "Pacific Heights": 10, "Russian Hill": 7,
            "Haight-Ashbury": 19, "Golden Gate Park": 23, "Fisherman's Wharf": 8,
            "Sunset District": 29, "The Castro": 22
        },
        "Embarcadero": {
            "Chinatown": 7, "Embarcadero": 0, "Pacific Heights": 11, "Russian Hill": 8,
            "Haight-Ashbury": 21, "Golden Gate Park": 25, "Fisherman's Wharf": 6,
            "Sunset District": 30, "The Castro": 25
        },
        "Pacific Heights": {
            "Chinatown": 11, "Embarcadero": 10, "Pacific Heights": 0, "Russian Hill": 7,
            "Haight-Ashbury": 11, "Golden Gate Park": 15, "Fisherman's Wharf": 13,
            "Sunset District": 21, "The Castro": 16
        },
        "Russian Hill": {
            "Chinatown": 9, "Embarcadero": 8, "Pacific Heights": 7, "Russian Hill": 0,
            "Haight-Ashbury": 17, "Golden Gate Park": 21, "Fisherman's Wharf": 7,
            "Sunset District": 23, "The Castro": 21
        },
        "Haight-Ashbury": {
            "Chinatown": 19, "Embarcadero": 20, "Pacific Heights": 12, "Russian Hill": 17,
            "Haight-Ashbury": 0, "Golden Gate Park": 7, "Fisherman's Wharf": 23,
            "Sunset District": 15, "The Castro": 6
        },
        "Golden Gate Park": {
            "Chinatown": 23, "Embarcadero": 25, "Pacific Heights": 16, "Russian Hill": 19,
            "Haight-Ashbury": 7, "Golden Gate Park": 0, "Fisherman's Wharf": 24,
            "Sunset District": 10, "The Castro": 13
        },
        "Fisherman's Wharf": {
            "Chinatown": 12, "Embarcadero": 8, "Pacific Heights": 12, "Russian Hill": 7,
            "Haight-Ashbury": 22, "Golden Gate Park": 25, "Fisherman's Wharf": 0,
            "Sunset District": 27, "The Castro": 27
        },
        "Sunset District": {
            "Chinatown": 30, "Embarcadero": 30, "Pacific Heights": 21, "Russian Hill": 24,
            "Haight-Ashbury": 15, "Golden Gate Park": 11, "Fisherman's Wharf": 29,
            "Sunset District": 0, "The Castro": 17
        },
        "The Castro": {
            "Chinatown": 22, "Embarcadero": 22, "Pacific Heights": 16, "Russian Hill": 18,
            "Haight-Ashbury": 6, "Golden Gate Park": 11, "Fisherman's Wharf": 24,
            "Sunset District": 17, "The Castro": 0
        }
    }
    
    # Friend constraints
    friends = {
        "Richard": {
            "location": "Embarcadero",
            "available_start": datetime.strptime("15:15", "%H:%M"),
            "available_end": datetime.strptime("18:45", "%H:%M"),
            "min_duration": 90  # minutes
        },
        "Mark": {
            "location": "Pacific Heights",
            "available_start": datetime.strptime("15:00", "%H:%M"),
            "available_end": datetime.strptime("17:00", "%H:%M"),
            "min_duration": 45
        },
        "Matthew": {
            "location": "Russian Hill",
            "available_start": datetime.strptime("17:30", "%H:%M"),
            "available_end": datetime.strptime("21:00", "%H:%M"),
            "min_duration": 90
        },
        "Rebecca": {
            "location": "Haight-Ashbury",
            "available_start": datetime.strptime("14:45", "%H:%M"),
            "available_end": datetime.strptime("18:00", "%H:%M"),
            "min_duration": 60
        },
        "Melissa": {
            "location": "Golden Gate Park",
            "available_start": datetime.strptime("13:45", "%H:%M"),
            "available_end": datetime.strptime("17:30", "%H:%M"),
            "min_duration": 90
        },
        "Margaret": {
            "location": "Fisherman's Wharf",
            "available_start": datetime.strptime("14:45", "%H:%M"),
            "available_end": datetime.strptime("20:15", "%H:%M"),
            "min_duration": 15
        },
        "Emily": {
            "location": "Sunset District",
            "available_start": datetime.strptime("15:45", "%H:%M"),
            "available_end": datetime.strptime("17:00", "%H:%M"),
            "min_duration": 45
        },
        "George": {
            "location": "The Castro",
            "available_start": datetime.strptime("14:00", "%H:%M"),
            "available_end": datetime.strptime("16:15", "%H:%M"),
            "min_duration": 75
        }
    }
    
    # Start time
    start_time = datetime.strptime("9:00", "%H:%M")
    current_location = "Chinatown"
    
    # Create problem
    problem = constraint.Problem()
    
    # Define variables for each friend: start time and duration
    for friend in friends:
        friend_data = friends[friend]
        available_start_minutes = (friend_data["available_start"] - start_time).total_seconds() / 60
        available_end_minutes = (friend_data["available_end"] - start_time).total_seconds() / 60
        min_duration = friend_data["min_duration"]
        
        # Add start time variable (in minutes from 9:00)
        problem.addVariable(f"{friend}_start", range(int(available_start_minutes), int(available_end_minutes - min_duration) + 1))
        
        # Add duration variable (at least min_duration)
        problem.addVariable(f"{friend}_duration", range(min_duration, int(available_end_minutes - available_start_minutes) + 1))
        
        # Add variable to indicate if we meet this friend (0 or 1)
        problem.addVariable(f"{friend}_meet", [0, 1])
    
    # Add constraints for travel time and scheduling
    friend_names = list(friends.keys())
    
    def travel_and_schedule_constraint(*args):
        # Extract all variables
        variables = {}
        for i, friend in enumerate(friend_names):
            variables[f"{friend}_start"] = args[i * 3]
            variables[f"{friend}_duration"] = args[i * 3 + 1]
            variables[f"{friend}_meet"] = args[i * 3 + 2]
        
        # Filter only friends we're meeting
        meeting_friends = []
        for friend in friend_names:
            if variables[f"{friend}_meet"] == 1:
                meeting_friends.append({
                    "name": friend,
                    "start": variables[f"{friend}_start"],
                    "duration": variables[f"{friend}_duration"],
                    "end": variables[f"{friend}_start"] + variables[f"{friend}_duration"],
                    "location": friends[friend]["location"]
                })
        
        # Sort by start time
        meeting_friends.sort(key=lambda x: x["start"])
        
        # Check if schedule is feasible with travel times
        current_time = 0  # Start at 9:00
        current_loc = "Chinatown"
        
        for i, meeting in enumerate(meeting_friends):
            # Travel to meeting location
            travel_time = travel_times[current_loc][meeting["location"]]
            
            # Check if we can arrive on time
            if current_time + travel_time > meeting["start"]:
                return False
            
            # Update current time and location
            current_time = meeting["end"]
            current_loc = meeting["location"]
        
        return True
    
    # Add the constraint function
    all_vars = []
    for friend in friend_names:
        all_vars.extend([f"{friend}_start", f"{friend}_duration", f"{friend}_meet"])
    
    problem.addConstraint(travel_and_schedule_constraint, all_vars)
    
    # Objective: maximize number of friends met
    def objective_function(*args):
        total_met = 0
        for i, friend in enumerate(friend_names):
            if args[i * 3 + 2] == 1:  # _meet variable
                total_met += 1
        return total_met
    
    # Find solution
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try to meet as many as possible with a simpler approach
        itinerary = []
        current_time = start_time
        current_loc = "Chinatown"
        
        # Try to meet friends in a greedy way
        for friend in friend_names:
            friend_data = friends[friend]
            travel_time = travel_times[current_loc][friend_data["location"]]
            arrival_time = current_time + timedelta(minutes=travel_time)
            
            # Check if we can meet this friend
            if (arrival_time >= friend_data["available_start"] and 
                arrival_time + timedelta(minutes=friend_data["min_duration"]) <= friend_data["available_end"]):
                
                # Add to itinerary
                start_meeting = max(arrival_time, friend_data["available_start"])
                end_meeting = start_meeting + timedelta(minutes=friend_data["min_duration"])
                
                itinerary.append({
                    "action": "meet",
                    "location": friend_data["location"],
                    "person": friend,
                    "start_time": start_meeting.strftime("%H:%M"),
                    "end_time": end_meeting.strftime("%H:%M")
                })
                
                current_time = end_meeting
                current_loc = friend_data["location"]
        
        result = {"itinerary": itinerary}
    else:
        # Find best solution (maximize number of friends met)
        best_solution = max(solutions, key=lambda sol: sum(sol[f"{friend}_meet"] for friend in friend_names))
        
        # Build itinerary from best solution
        itinerary = []
        meeting_events = []
        
        for friend in friend_names:
            if best_solution[f"{friend}_meet"] == 1:
                start_minutes = best_solution[f"{friend}_start"]
                duration = best_solution[f"{friend}_duration"]
                
                start_time_meeting = start_time + timedelta(minutes=start_minutes)
                end_time_meeting = start_time_meeting + timedelta(minutes=duration)
                
                meeting_events.append({
                    "friend": friend,
                    "location": friends[friend]["location"],
                    "start": start_time_meeting,
                    "end": end_time_meeting
                })
        
        # Sort by start time
        meeting_events.sort(key=lambda x: x["start"])
        
        # Add travel from Chinatown to first meeting
        if meeting_events:
            first_meeting = meeting_events[0]
            travel_time = travel_times["Chinatown"][first_meeting["location"]]
            departure_time = first_meeting["start"] - timedelta(minutes=travel_time)
            
            # Verify we're not departing before 9:00
            if departure_time < start_time:
                departure_time = start_time
        
        # Build final itinerary
        for event in meeting_events:
            itinerary.append({
                "action": "meet",
                "location": event["location"],
                "person": event["friend"],
                "start_time": event["start"].strftime("%H:%M"),
                "end_time": event["end"].strftime("%H:%M")
            })
        
        result = {"itinerary": itinerary}
    
    # Output as JSON
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()