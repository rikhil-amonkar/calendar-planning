import json
from datetime import datetime, timedelta

def main():
    # Define locations
    locations = [
        "Sunset District", "Russian Hill", "The Castro", "Richmond District",
        "Marina District", "North Beach", "Union Square", "Golden Gate Park"
    ]
    
    # Travel time matrix (minutes)
    travel_times = {
        ("Sunset District", "Russian Hill"): 24,
        ("Sunset District", "The Castro"): 17,
        ("Sunset District", "Richmond District"): 12,
        ("Sunset District", "Marina District"): 21,
        ("Sunset District", "North Beach"): 29,
        ("Sunset District", "Union Square"): 30,
        ("Sunset District", "Golden Gate Park"): 11,
        ("Russian Hill", "Sunset District"): 23,
        ("Russian Hill", "The Castro"): 21,
        ("Russian Hill", "Richmond District"): 14,
        ("Russian Hill", "Marina District"): 7,
        ("Russian Hill", "North Beach"): 5,
        ("Russian Hill", "Union Square"): 11,
        ("Russian Hill", "Golden Gate Park"): 21,
        ("The Castro", "Sunset District"): 17,
        ("The Castro", "Russian Hill"): 18,
        ("The Castro", "Richmond District"): 16,
        ("The Castro", "Marina District"): 21,
        ("The Castro", "North Beach"): 20,
        ("The Castro", "Union Square"): 19,
        ("The Castro", "Golden Gate Park"): 11,
        ("Richmond District", "Sunset District"): 11,
        ("Richmond District", "Russian Hill"): 13,
        ("Richmond District", "The Castro"): 16,
        ("Richmond District", "Marina District"): 9,
        ("Richmond District", "North Beach"): 17,
        ("Richmond District", "Union Square"): 21,
        ("Richmond District", "Golden Gate Park"): 9,
        ("Marina District", "Sunset District"): 19,
        ("Marina District", "Russian Hill"): 8,
        ("Marina District", "The Castro"): 22,
        ("Marina District", "Richmond District"): 11,
        ("Marina District", "North Beach"): 11,
        ("Marina District", "Union Square"): 16,
        ("Marina District", "Golden Gate Park"): 18,
        ("North Beach", "Sunset District"): 27,
        ("North Beach", "Russian Hill"): 4,
        ("North Beach", "The Castro"): 22,
        ("North Beach", "Richmond District"): 18,
        ("North Beach", "Marina District"): 9,
        ("North Beach", "Union Square"): 7,
        ("North Beach", "Golden Gate Park"): 22,
        ("Union Square", "Sunset District"): 26,
        ("Union Square", "Russian Hill"): 13,
        ("Union Square", "The Castro"): 19,
        ("Union Square", "Richmond District"): 20,
        ("Union Square", "Marina District"): 18,
        ("Union Square", "North Beach"): 10,
        ("Union Square", "Golden Gate Park"): 22,
        ("Golden Gate Park", "Sunset District"): 10,
        ("Golden Gate Park", "Russian Hill"): 19,
        ("Golden Gate Park", "The Castro"): 13,
        ("Golden Gate Park", "Richmond District"): 7,
        ("Golden Gate Park", "Marina District"): 16,
        ("Golden Gate Park", "North Beach"): 24,
        ("Golden Gate Park", "Union Square"): 22,
    }
    
    # Friend constraints
    friends = {
        "Karen": {
            "location": "Russian Hill",
            "available_start": "20:45",  # 8:45 PM
            "available_end": "21:45",    # 9:45 PM
            "min_duration": 60
        },
        "Jessica": {
            "location": "The Castro",
            "available_start": "15:45",  # 3:45 PM
            "available_end": "19:30",    # 7:30 PM
            "min_duration": 60
        },
        "Matthew": {
            "location": "Richmond District",
            "available_start": "7:30",   # 7:30 AM
            "available_end": "15:15",    # 3:15 PM
            "min_duration": 15
        },
        "Michelle": {
            "location": "Marina District",
            "available_start": "10:30",  # 10:30 AM
            "available_end": "18:45",    # 6:45 PM
            "min_duration": 75
        },
        "Carol": {
            "location": "North Beach",
            "available_start": "12:00",  # 12:00 PM
            "available_end": "17:00",    # 5:00 PM
            "min_duration": 90
        },
        "Stephanie": {
            "location": "Union Square",
            "available_start": "10:45",  # 10:45 AM
            "available_end": "14:15",    # 2:15 PM
            "min_duration": 30
        },
        "Linda": {
            "location": "Golden Gate Park",
            "available_start": "10:45",  # 10:45 AM
            "available_end": "22:00",    # 10:00 PM
            "min_duration": 90
        }
    }
    
    # Convert time strings to minutes since midnight
    def time_to_minutes(time_str):
        hours, minutes = map(int, time_str.split(':'))
        return hours * 60 + minutes
    
    def minutes_to_time(minutes):
        hours = minutes // 60
        mins = minutes % 60
        return f"{hours}:{mins:02d}"
    
    # Convert friend availability to minutes
    for friend in friends:
        friends[friend]["available_start_min"] = time_to_minutes(friends[friend]["available_start"])
        friends[friend]["available_end_min"] = time_to_minutes(friends[friend]["available_end"])
    
    # Start time (9:00 AM)
    start_time_minutes = time_to_minutes("9:00")
    
    def can_schedule(meeting1, meeting2):
        """Check if two meetings can be scheduled considering travel time"""
        travel_key = (meeting1["location"], meeting2["location"])
        travel_time = travel_times.get(travel_key, 999)
        
        # Check if meeting1 ends early enough for travel to meeting2
        if meeting1["end"] + travel_time <= meeting2["start"]:
            return True
        
        # Check if meeting2 ends early enough for travel to meeting1
        if meeting2["end"] + travel_time <= meeting1["start"]:
            return True
        
        return False
    
    def find_best_schedule(current_schedule, remaining_friends, current_time, current_location):
        """Recursive function to find the best schedule"""
        if not remaining_friends:
            return current_schedule
        
        best_schedule = current_schedule
        
        for friend in list(remaining_friends):
            friend_info = friends[friend]
            
            # Calculate earliest possible start time
            earliest_start = max(
                friend_info["available_start_min"],
                current_time + (travel_times.get((current_location, friend_info["location"]), 0) if current_location else 0)
            )
            
            # Check if meeting is possible within availability
            if earliest_start <= friend_info["available_end_min"] - friend_info["min_duration"]:
                # Schedule the meeting at earliest possible time
                meeting_start = earliest_start
                meeting_end = meeting_start + friend_info["min_duration"]
                
                # Ensure meeting doesn't exceed availability
                if meeting_end <= friend_info["available_end_min"]:
                    new_meeting = {
                        "friend": friend,
                        "location": friend_info["location"],
                        "start": meeting_start,
                        "end": meeting_end
                    }
                    
                    # Check if this meeting conflicts with any already scheduled
                    conflict = False
                    for scheduled in current_schedule:
                        if not can_schedule(new_meeting, scheduled):
                            conflict = True
                            break
                    
                    if not conflict:
                        new_schedule = current_schedule + [new_meeting]
                        new_remaining = remaining_friends - {friend}
                        
                        # Recursively try to schedule remaining friends
                        candidate_schedule = find_best_schedule(
                            new_schedule, new_remaining, meeting_end, friend_info["location"]
                        )
                        
                        if len(candidate_schedule) > len(best_schedule):
                            best_schedule = candidate_schedule
        
        return best_schedule
    
    # Try different starting points to find the best schedule
    all_friends = set(friends.keys())
    best_overall_schedule = []
    
    # Try starting with each friend who is available at 9:00 AM
    for starting_friend in all_friends:
        friend_info = friends[starting_friend]
        if friend_info["available_start_min"] <= start_time_minutes <= friend_info["available_end_min"] - friend_info["min_duration"]:
            initial_meeting = {
                "friend": starting_friend,
                "location": friend_info["location"],
                "start": start_time_minutes,
                "end": start_time_minutes + friend_info["min_duration"]
            }
            
            remaining_friends = all_friends - {starting_friend}
            candidate_schedule = find_best_schedule(
                [initial_meeting], remaining_friends, 
                start_time_minutes + friend_info["min_duration"], friend_info["location"]
            )
            
            if len(candidate_schedule) > len(best_overall_schedule):
                best_overall_schedule = candidate_schedule
    
    # If no schedule found starting at 9:00, try flexible start
    if not best_overall_schedule:
        for starting_friend in all_friends:
            friend_info = friends[starting_friend]
            earliest_start = max(friend_info["available_start_min"], start_time_minutes)
            if earliest_start <= friend_info["available_end_min"] - friend_info["min_duration"]:
                initial_meeting = {
                    "friend": starting_friend,
                    "location": friend_info["location"],
                    "start": earliest_start,
                    "end": earliest_start + friend_info["min_duration"]
                }
                
                remaining_friends = all_friends - {starting_friend}
                candidate_schedule = find_best_schedule(
                    [initial_meeting], remaining_friends, 
                    earliest_start + friend_info["min_duration"], friend_info["location"]
                )
                
                if len(candidate_schedule) > len(best_overall_schedule):
                    best_overall_schedule = candidate_schedule
    
    # Sort the final schedule by start time
    best_overall_schedule.sort(key=lambda x: x["start"])
    
    # Build itinerary
    itinerary = []
    for meeting in best_overall_schedule:
        itinerary.append({
            "action": "meet",
            "location": meeting["location"],
            "person": meeting["friend"],
            "start_time": minutes_to_time(meeting["start"]),
            "end_time": minutes_to_time(meeting["end"])
        })
    
    # Output result
    result = {
        "itinerary": itinerary
    }
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()