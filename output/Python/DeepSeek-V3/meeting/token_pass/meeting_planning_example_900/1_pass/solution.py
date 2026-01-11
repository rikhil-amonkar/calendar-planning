import json
from itertools import permutations
from datetime import datetime, timedelta

def parse_time(time_str):
    """Convert time string to minutes since midnight"""
    if 'AM' in time_str or 'PM' in time_str:
        time_str = time_str.replace('AM', '').replace('PM', '').strip()
        if 'PM' in time_str:
            # Handle PM times
            time_str = time_str.replace('PM', '').strip()
            hour, minute = map(int, time_str.split(':'))
            if hour != 12:
                hour += 12
        else:
            # Handle AM times
            time_str = time_str.replace('AM', '').strip()
            hour, minute = map(int, time_str.split(':'))
            if hour == 12:
                hour = 0
    else:
        hour, minute = map(int, time_str.split(':'))
    
    return hour * 60 + minute

def format_time(minutes):
    """Convert minutes since midnight to time string"""
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

class MeetingPlanner:
    def __init__(self):
        # Initialize travel times matrix
        self.locations = [
            "Richmond District", "The Castro", "Nob Hill", "Marina District",
            "Pacific Heights", "Haight-Ashbury", "Mission District", "Chinatown",
            "Russian Hill", "Alamo Square", "Bayview"
        ]
        
        # Create travel time dictionary
        self.travel_times = {}
        
        # Add all travel times from the problem statement
        travel_data = [
            ("Richmond District", "The Castro", 16),
            ("Richmond District", "Nob Hill", 17),
            ("Richmond District", "Marina District", 9),
            ("Richmond District", "Pacific Heights", 10),
            ("Richmond District", "Haight-Ashbury", 10),
            ("Richmond District", "Mission District", 20),
            ("Richmond District", "Chinatown", 20),
            ("Richmond District", "Russian Hill", 13),
            ("Richmond District", "Alamo Square", 13),
            ("Richmond District", "Bayview", 27),
            ("The Castro", "Richmond District", 16),
            ("The Castro", "Nob Hill", 16),
            ("The Castro", "Marina District", 21),
            ("The Castro", "Pacific Heights", 16),
            ("The Castro", "Haight-Ashbury", 6),
            ("The Castro", "Mission District", 7),
            ("The Castro", "Chinatown", 22),
            ("The Castro", "Russian Hill", 18),
            ("The Castro", "Alamo Square", 8),
            ("The Castro", "Bayview", 19),
            ("Nob Hill", "Richmond District", 14),
            ("Nob Hill", "The Castro", 17),
            ("Nob Hill", "Marina District", 11),
            ("Nob Hill", "Pacific Heights", 8),
            ("Nob Hill", "Haight-Ashbury", 13),
            ("Nob Hill", "Mission District", 13),
            ("Nob Hill", "Chinatown", 6),
            ("Nob Hill", "Russian Hill", 5),
            ("Nob Hill", "Alamo Square", 11),
            ("Nob Hill", "Bayview", 19),
            ("Marina District", "Richmond District", 11),
            ("Marina District", "The Castro", 22),
            ("Marina District", "Nob Hill", 12),
            ("Marina District", "Pacific Heights", 7),
            ("Marina District", "Haight-Ashbury", 16),
            ("Marina District", "Mission District", 20),
            ("Marina District", "Chinatown", 15),
            ("Marina District", "Russian Hill", 8),
            ("Marina District", "Alamo Square", 15),
            ("Marina District", "Bayview", 27),
            ("Pacific Heights", "Richmond District", 12),
            ("Pacific Heights", "The Castro", 16),
            ("Pacific Heights", "Nob Hill", 8),
            ("Pacific Heights", "Marina District", 6),
            ("Pacific Heights", "Haight-Ashbury", 11),
            ("Pacific Heights", "Mission District", 15),
            ("Pacific Heights", "Chinatown", 11),
            ("Pacific Heights", "Russian Hill", 7),
            ("Pacific Heights", "Alamo Square", 10),
            ("Pacific Heights", "Bayview", 22),
            ("Haight-Ashbury", "Richmond District", 10),
            ("Haight-Ashbury", "The Castro", 6),
            ("Haight-Ashbury", "Nob Hill", 15),
            ("Haight-Ashbury", "Marina District", 17),
            ("Haight-Ashbury", "Pacific Heights", 12),
            ("Haight-Ashbury", "Mission District", 11),
            ("Haight-Ashbury", "Chinatown", 19),
            ("Haight-Ashbury", "Russian Hill", 17),
            ("Haight-Ashbury", "Alamo Square", 5),
            ("Haight-Ashbury", "Bayview", 18),
            ("Mission District", "Richmond District", 20),
            ("Mission District", "The Castro", 7),
            ("Mission District", "Nob Hill", 12),
            ("Mission District", "Marina District", 19),
            ("Mission District", "Pacific Heights", 16),
            ("Mission District", "Haight-Ashbury", 12),
            ("Mission District", "Chinatown", 16),
            ("Mission District", "Russian Hill", 15),
            ("Mission District", "Alamo Square", 11),
            ("Mission District", "Bayview", 14),
            ("Chinatown", "Richmond District", 20),
            ("Chinatown", "The Castro", 22),
            ("Chinatown", "Nob Hill", 9),
            ("Chinatown", "Marina District", 12),
            ("Chinatown", "Pacific Heights", 10),
            ("Chinatown", "Haight-Ashbury", 19),
            ("Chinatown", "Mission District", 17),
            ("Chinatown", "Russian Hill", 7),
            ("Chinatown", "Alamo Square", 17),
            ("Chinatown", "Bayview", 20),
            ("Russian Hill", "Richmond District", 14),
            ("Russian Hill", "The Castro", 21),
            ("Russian Hill", "Nob Hill", 5),
            ("Russian Hill", "Marina District", 7),
            ("Russian Hill", "Pacific Heights", 7),
            ("Russian Hill", "Haight-Ashbury", 17),
            ("Russian Hill", "Mission District", 16),
            ("Russian Hill", "Chinatown", 9),
            ("Russian Hill", "Alamo Square", 15),
            ("Russian Hill", "Bayview", 23),
            ("Alamo Square", "Richmond District", 11),
            ("Alamo Square", "The Castro", 8),
            ("Alamo Square", "Nob Hill", 11),
            ("Alamo Square", "Marina District", 15),
            ("Alamo Square", "Pacific Heights", 10),
            ("Alamo Square", "Haight-Ashbury", 5),
            ("Alamo Square", "Mission District", 10),
            ("Alamo Square", "Chinatown", 15),
            ("Alamo Square", "Russian Hill", 13),
            ("Alamo Square", "Bayview", 16),
            ("Bayview", "Richmond District", 25),
            ("Bayview", "The Castro", 19),
            ("Bayview", "Nob Hill", 20),
            ("Bayview", "Marina District", 27),
            ("Bayview", "Pacific Heights", 23),
            ("Bayview", "Haight-Ashbury", 19),
            ("Bayview", "Mission District", 13),
            ("Bayview", "Chinatown", 19),
            ("Bayview", "Russian Hill", 23),
            ("Bayview", "Alamo Square", 16)
        ]
        
        for from_loc, to_loc, time in travel_data:
            self.travel_times[(from_loc, to_loc)] = time
        
        # Define meeting constraints
        self.meetings = [
            {
                "person": "Matthew",
                "location": "The Castro",
                "available_start": parse_time("4:30PM"),
                "available_end": parse_time("8:00PM"),
                "min_duration": 45
            },
            {
                "person": "Rebecca",
                "location": "Nob Hill",
                "available_start": parse_time("3:15PM"),
                "available_end": parse_time("7:15PM"),
                "min_duration": 105
            },
            {
                "person": "Brian",
                "location": "Marina District",
                "available_start": parse_time("2:15PM"),
                "available_end": parse_time("10:00PM"),
                "min_duration": 30
            },
            {
                "person": "Emily",
                "location": "Pacific Heights",
                "available_start": parse_time("11:15AM"),
                "available_end": parse_time("7:45PM"),
                "min_duration": 15
            },
            {
                "person": "Karen",
                "location": "Haight-Ashbury",
                "available_start": parse_time("11:45AM"),
                "available_end": parse_time("5:30PM"),
                "min_duration": 30
            },
            {
                "person": "Stephanie",
                "location": "Mission District",
                "available_start": parse_time("1:00PM"),
                "available_end": parse_time("3:45PM"),
                "min_duration": 75
            },
            {
                "person": "James",
                "location": "Chinatown",
                "available_start": parse_time("2:30PM"),
                "available_end": parse_time("7:00PM"),
                "min_duration": 120
            },
            {
                "person": "Steven",
                "location": "Russian Hill",
                "available_start": parse_time("2:00PM"),
                "available_end": parse_time("8:00PM"),
                "min_duration": 30
            },
            {
                "person": "Elizabeth",
                "location": "Alamo Square",
                "available_start": parse_time("1:00PM"),
                "available_end": parse_time("5:15PM"),
                "min_duration": 120
            },
            {
                "person": "William",
                "location": "Bayview",
                "available_start": parse_time("6:15PM"),
                "available_end": parse_time("8:15PM"),
                "min_duration": 90
            }
        ]
        
        # Start at Richmond District at 9:00 AM
        self.start_time = parse_time("9:00AM")
        self.start_location = "Richmond District"
        
    def get_travel_time(self, from_loc, to_loc):
        """Get travel time between two locations"""
        if from_loc == to_loc:
            return 0
        return self.travel_times.get((from_loc, to_loc), 999)  # Large number if not found
    
    def find_best_schedule(self):
        """Find the best schedule using backtracking search"""
        best_schedule = []
        best_score = -1
        
        # Try different orders of meetings
        # Since trying all permutations of 10 meetings is too large (10! = 3.6M),
        # we'll use a heuristic approach: try meetings in different priority orders
        
        # Define priority orders based on time windows and durations
        priority_orders = [
            # Order by earliest available start time
            sorted(self.meetings, key=lambda m: m["available_start"]),
            # Order by latest available end time
            sorted(self.meetings, key=lambda m: m["available_end"], reverse=True),
            # Order by shortest minimum duration
            sorted(self.meetings, key=lambda m: m["min_duration"]),
            # Order by longest minimum duration
            sorted(self.meetings, key=lambda m: m["min_duration"], reverse=True),
            # Order by location proximity (heuristic)
            self.meetings  # Original order
        ]
        
        for meeting_order in priority_orders:
            schedule = []
            current_time = self.start_time
            current_location = self.start_location
            
            for meeting in meeting_order:
                # Calculate travel time to meeting location
                travel_time = self.get_travel_time(current_location, meeting["location"])
                arrival_time = current_time + travel_time
                
                # Check if we can arrive during available window
                if arrival_time < meeting["available_start"]:
                    # Wait until meeting starts
                    arrival_time = meeting["available_start"]
                
                # Check if we can meet for minimum duration
                end_time = arrival_time + meeting["min_duration"]
                
                if end_time <= meeting["available_end"] and end_time <= parse_time("11:59PM"):
                    # Schedule the meeting
                    schedule.append({
                        "person": meeting["person"],
                        "location": meeting["location"],
                        "start_time": arrival_time,
                        "end_time": end_time
                    })
                    
                    # Update current time and location
                    current_time = end_time
                    current_location = meeting["location"]
            
            # Calculate score (number of meetings scheduled)
            score = len(schedule)
            
            if score > best_score:
                best_score = score
                best_schedule = schedule
        
        # Try to improve schedule by adjusting meeting times
        improved_schedule = self.optimize_schedule(best_schedule)
        
        return improved_schedule
    
    def optimize_schedule(self, schedule):
        """Try to optimize the schedule by adjusting meeting times"""
        if not schedule:
            return schedule
        
        optimized = []
        current_time = self.start_time
        current_location = self.start_location
        
        for i, meeting_slot in enumerate(schedule):
            # Find the corresponding meeting constraints
            meeting_info = None
            for m in self.meetings:
                if m["person"] == meeting_slot["person"]:
                    meeting_info = m
                    break
            
            if not meeting_info:
                continue
            
            # Calculate travel time
            travel_time = self.get_travel_time(current_location, meeting_info["location"])
            earliest_arrival = current_time + travel_time
            
            # If we arrive early, we might be able to start the meeting earlier
            if earliest_arrival < meeting_info["available_start"]:
                arrival_time = meeting_info["available_start"]
            else:
                arrival_time = earliest_arrival
            
            # Calculate end time
            end_time = arrival_time + meeting_info["min_duration"]
            
            # Ensure we don't exceed available end time
            if end_time > meeting_info["available_end"]:
                # Need to start earlier
                end_time = meeting_info["available_end"]
                arrival_time = end_time - meeting_info["min_duration"]
                
                # Ensure we don't start before we can arrive
                if arrival_time < earliest_arrival:
                    arrival_time = earliest_arrival
                    end_time = arrival_time + meeting_info["min_duration"]
            
            optimized.append({
                "person": meeting_info["person"],
                "location": meeting_info["location"],
                "start_time": arrival_time,
                "end_time": end_time
            })
            
            current_time = end_time
            current_location = meeting_info["location"]
        
        return optimized
    
    def format_schedule(self, schedule):
        """Format schedule as required JSON output"""
        itinerary = []
        
        for meeting in schedule:
            itinerary.append({
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": format_time(meeting["start_time"]),
                "end_time": format_time(meeting["end_time"])
            })
        
        return {"itinerary": itinerary}

def main():
    planner = MeetingPlanner()
    schedule = planner.find_best_schedule()
    result = planner.format_schedule(schedule)
    
    # Print JSON result
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()