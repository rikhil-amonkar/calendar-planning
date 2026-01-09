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
    
    def can_meet_friend(current_time, current_loc, friend_name, friend_data):
        """Check if we can meet a friend given current time and location"""
        travel_time = travel_times[current_loc][friend_data["location"]]
        arrival_time = current_time + timedelta(minutes=travel_time)
        
        # Check if we arrive during friend's availability
        if arrival_time < friend_data["available_start"]:
            arrival_time = friend_data["available_start"]
        
        end_time = arrival_time + timedelta(minutes=friend_data["min_duration"])
        
        # Check if the entire meeting fits within friend's availability
        if (arrival_time >= friend_data["available_start"] and 
            end_time <= friend_data["available_end"]):
            return True, arrival_time, end_time
        
        return False, None, None
    
    def find_best_itinerary(current_time, current_loc, visited, itinerary, max_depth=8):
        """Recursive function to find the best itinerary using backtracking"""
        if len(visited) == len(friends) or max_depth == 0:
            return itinerary.copy()
        
        best_itinerary = itinerary.copy()
        
        for friend_name, friend_data in friends.items():
            if friend_name in visited:
                continue
                
            can_meet, arrival_time, end_time = can_meet_friend(current_time, current_loc, friend_name, friend_data)
            
            if can_meet:
                # Add this friend to visited and itinerary
                visited.add(friend_name)
                new_itinerary = itinerary + [{
                    "action": "meet",
                    "location": friend_data["location"],
                    "person": friend_name,
                    "start_time": arrival_time.strftime("%H:%M"),
                    "end_time": end_time.strftime("%H:%M")
                }]
                
                # Recursively find best continuation
                candidate_itinerary = find_best_itinerary(
                    end_time, 
                    friend_data["location"], 
                    visited, 
                    new_itinerary, 
                    max_depth - 1
                )
                
                # Keep the best itinerary
                if len(candidate_itinerary) > len(best_itinerary):
                    best_itinerary = candidate_itinerary
                
                # Backtrack
                visited.remove(friend_name)
        
        return best_itinerary
    
    # Find the best itinerary
    best_itinerary = find_best_itinerary(start_time, current_location, set(), [])
    
    # Sort itinerary by start time for final output
    best_itinerary.sort(key=lambda x: datetime.strptime(x["start_time"], "%H:%M"))
    
    result = {"itinerary": best_itinerary}
    
    # Output as JSON
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()