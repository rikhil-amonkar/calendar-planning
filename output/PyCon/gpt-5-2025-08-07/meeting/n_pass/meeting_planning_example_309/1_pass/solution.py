import constraint
from datetime import datetime, timedelta
import json

def main():
    # Define locations
    locations = ["Financial District", "Chinatown", "Alamo Square", "Bayview", "Fisherman's Wharf"]
    
    # Travel times in minutes (from row to column)
    travel_times = {
        "Financial District": {
            "Financial District": 0,
            "Chinatown": 5,
            "Alamo Square": 17,
            "Bayview": 19,
            "Fisherman's Wharf": 10
        },
        "Chinatown": {
            "Financial District": 5,
            "Chinatown": 0,
            "Alamo Square": 17,
            "Bayview": 22,
            "Fisherman's Wharf": 8
        },
        "Alamo Square": {
            "Financial District": 17,
            "Chinatown": 16,
            "Alamo Square": 0,
            "Bayview": 16,
            "Fisherman's Wharf": 19
        },
        "Bayview": {
            "Financial District": 19,
            "Chinatown": 18,
            "Alamo Square": 16,
            "Bayview": 0,
            "Fisherman's Wharf": 25
        },
        "Fisherman's Wharf": {
            "Financial District": 11,
            "Chinatown": 12,
            "Alamo Square": 20,
            "Bayview": 26,
            "Fisherman's Wharf": 0
        }
    }
    
    # Friend constraints
    friends = {
        "Nancy": {
            "location": "Chinatown",
            "available_start": datetime.strptime("9:30", "%H:%M"),
            "available_end": datetime.strptime("13:30", "%H:%M"),
            "min_duration": 90  # minutes
        },
        "Mary": {
            "location": "Alamo Square",
            "available_start": datetime.strptime("7:00", "%H:%M"),
            "available_end": datetime.strptime("21:00", "%H:%M"),
            "min_duration": 75  # minutes
        },
        "Jessica": {
            "location": "Bayview",
            "available_start": datetime.strptime("11:15", "%H:%M"),
            "available_end": datetime.strptime("13:45", "%H:%M"),
            "min_duration": 45  # minutes
        },
        "Rebecca": {
            "location": "Fisherman's Wharf",
            "available_start": datetime.strptime("7:00", "%H:%M"),
            "available_end": datetime.strptime("8:30", "%H:%M"),
            "min_duration": 45  # minutes
        }
    }
    
    # Start time
    start_time = datetime.strptime("9:00", "%H:%M")
    current_location = "Financial District"
    
    # Create problem
    problem = constraint.Problem()
    
    # We'll try to meet as many friends as possible
    # Since Rebecca is only available before we start, we can't meet her
    # So we focus on Nancy, Mary, and Jessica
    
    # Define variables for each potential meeting
    # We'll use binary variables to indicate if we meet each friend
    for friend in ["Nancy", "Mary", "Jessica"]:
        problem.addVariable(f"meet_{friend}", [0, 1])
    
    # If we meet a friend, we need to schedule start and end times
    for friend in ["Nancy", "Mary", "Jessica"]:
        friend_info = friends[friend]
        available_minutes = int((friend_info["available_end"] - friend_info["available_start"]).total_seconds() / 60)
        
        # Start time offset from available start (in minutes)
        problem.addVariable(f"start_offset_{friend}", range(0, available_minutes - friend_info["min_duration"] + 1))
        
        # Duration (at least min_duration, up to remaining available time)
        problem.addVariable(f"duration_{friend}", range(friend_info["min_duration"], available_minutes + 1))
    
    # Add constraints for valid meetings
    def meeting_constraints(meet_nancy, meet_mary, meet_jessica, 
                           start_offset_nancy, start_offset_mary, start_offset_jessica,
                           duration_nancy, duration_mary, duration_jessica):
        
        meetings = []
        if meet_nancy:
            nancy_start = friends["Nancy"]["available_start"] + timedelta(minutes=start_offset_nancy)
            nancy_end = nancy_start + timedelta(minutes=duration_nancy)
            meetings.append(("Nancy", "Chinatown", nancy_start, nancy_end))
        
        if meet_mary:
            mary_start = friends["Mary"]["available_start"] + timedelta(minutes=start_offset_mary)
            mary_end = mary_start + timedelta(minutes=duration_mary)
            meetings.append(("Mary", "Alamo Square", mary_start, mary_end))
        
        if meet_jessica:
            jessica_start = friends["Jessica"]["available_start"] + timedelta(minutes=start_offset_jessica)
            jessica_end = jessica_start + timedelta(minutes=duration_jessica)
            meetings.append(("Jessica", "Bayview", jessica_start, jessica_end))
        
        # Sort meetings by start time
        meetings.sort(key=lambda x: x[2])
        
        # Check if we can make all meetings with travel time
        current_time = start_time
        current_loc = "Financial District"
        
        for meeting in meetings:
            person, location, m_start, m_end = meeting
            
            # Travel to meeting location
            travel_time = travel_times[current_loc][location]
            arrival_time = current_time + timedelta(minutes=travel_time)
            
            # We need to arrive before or at the meeting start time
            if arrival_time > m_start:
                return False
            
            # Update current time and location
            current_time = m_end
            current_loc = location
        
        return True
    
    # Add the constraint function
    problem.addConstraint(meeting_constraints, 
                         ["meet_Nancy", "meet_Mary", "meet_Jessica",
                          "start_offset_Nancy", "start_offset_Mary", "start_offset_Jessica",
                          "duration_Nancy", "duration_Mary", "duration_Jessica"])
    
    # Find solution that maximizes number of meetings
    solutions = problem.getSolutions()
    
    if not solutions:
        # Fallback: try meetings one by one
        best_solution = None
        best_count = 0
        
        # Try different combinations
        for nancy in [0, 1]:
            for mary in [0, 1]:
                for jessica in [0, 1]:
                    test_solution = {
                        "meet_Nancy": nancy,
                        "meet_Mary": mary,
                        "meet_Jessica": jessica,
                        "start_offset_Nancy": 0,
                        "start_offset_Mary": 0,
                        "start_offset_Jessica": 0,
                        "duration_Nancy": friends["Nancy"]["min_duration"],
                        "duration_Mary": friends["Mary"]["min_duration"],
                        "duration_Jessica": friends["Jessica"]["min_duration"]
                    }
                    
                    if meeting_constraints(nancy, mary, jessica, 0, 0, 0,
                                          friends["Nancy"]["min_duration"],
                                          friends["Mary"]["min_duration"],
                                          friends["Jessica"]["min_duration"]):
                        count = nancy + mary + jessica
                        if count > best_count:
                            best_count = count
                            best_solution = test_solution
        
        if best_solution:
            solution = best_solution
        else:
            # Default fallback - just meet Mary who has the widest availability
            solution = {
                "meet_Nancy": 0,
                "meet_Mary": 1,
                "meet_Jessica": 0,
                "start_offset_Nancy": 0,
                "start_offset_Mary": 0,
                "start_offset_Jessica": 0,
                "duration_Nancy": friends["Nancy"]["min_duration"],
                "duration_Mary": friends["Mary"]["min_duration"],
                "duration_Jessica": friends["Jessica"]["min_duration"]
            }
    else:
        # Find solution with maximum meetings
        max_meetings = 0
        solution = None
        
        for sol in solutions:
            meetings_count = sol["meet_Nancy"] + sol["meet_Mary"] + sol["meet_Jessica"]
            if meetings_count > max_meetings:
                max_meetings = meetings_count
                solution = sol
    
    # Build itinerary
    itinerary = []
    current_time = start_time
    current_loc = "Financial District"
    
    # Create list of meetings in chronological order
    meetings = []
    
    if solution["meet_Nancy"]:
        nancy_start = friends["Nancy"]["available_start"] + timedelta(minutes=solution["start_offset_Nancy"])
        nancy_end = nancy_start + timedelta(minutes=solution["duration_Nancy"])
        meetings.append(("Nancy", "Chinatown", nancy_start, nancy_end))
    
    if solution["meet_Mary"]:
        mary_start = friends["Mary"]["available_start"] + timedelta(minutes=solution["start_offset_Mary"])
        mary_end = mary_start + timedelta(minutes=solution["duration_Mary"])
        meetings.append(("Mary", "Alamo Square", mary_start, mary_end))
    
    if solution["meet_Jessica"]:
        jessica_start = friends["Jessica"]["available_start"] + timedelta(minutes=solution["start_offset_Jessica"])
        jessica_end = jessica_start + timedelta(minutes=solution["duration_Jessica"])
        meetings.append(("Jessica", "Bayview", jessica_start, jessica_end))
    
    # Sort meetings by start time
    meetings.sort(key=lambda x: x[2])
    
    # Build final itinerary
    for person, location, start, end in meetings:
        # Add travel if needed
        if current_loc != location:
            travel_time = travel_times[current_loc][location]
            travel_start = current_time
            travel_end = current_time + timedelta(minutes=travel_time)
            
            itinerary.append({
                "action": "travel",
                "location": location,
                "person": None,
                "start_time": travel_start.strftime("%H:%M"),
                "end_time": travel_end.strftime("%H:%M")
            })
            
            current_time = travel_end
            current_loc = location
        
        # Add meeting
        itinerary.append({
            "action": "meet",
            "location": location,
            "person": person,
            "start_time": start.strftime("%H:%M"),
            "end_time": end.strftime("%H:%M")
        })
        
        current_time = end
        current_loc = location
    
    # Output result
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()