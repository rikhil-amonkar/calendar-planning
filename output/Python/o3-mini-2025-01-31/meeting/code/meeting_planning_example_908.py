import json

# Convert time in minutes to "H:MM" string (24-hour format, no leading zero for hour)
def minutes_to_time_str(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

# Travel times dictionary between locations (in minutes)
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
    ("Sunset District", "Union Square"): 30
}

# Define meeting constraints for each friend.
# Times are converted to minutes from midnight.
meeting_constraints = [
    {
        "person": "Mark",
        "location": "Fisherman's Wharf",
        "avail_start": 8*60 + 15,    # 8:15
        "avail_end": 10*60,          # 10:00
        "min_duration": 30
    },
    {
        "person": "Stephanie",
        "location": "Presidio",
        "avail_start": 12*60 + 15,   # 12:15
        "avail_end": 15*60,          # 15:00
        "min_duration": 75
    },
    {
        "person": "Betty",
        "location": "Bayview",
        "avail_start": 7*60 + 15,    # 7:15
        "avail_end": 20*60 + 30,     # 20:30
        "min_duration": 15
    },
    {
        "person": "Lisa",
        "location": "Haight-Ashbury",
        "avail_start": 15*60 + 30,   # 15:30
        "avail_end": 18*60 + 30,     # 18:30
        "min_duration": 45
    },
    {
        "person": "William",
        "location": "Russian Hill",
        "avail_start": 18*60 + 45,   # 18:45
        "avail_end": 20*60,          # 20:00
        "min_duration": 60
    },
    {
        "person": "Brian",
        "location": "The Castro",
        "avail_start": 9*60 + 15,    # 9:15
        "avail_end": 13*60 + 15,     # 13:15
        "min_duration": 30
    },
    {
        "person": "Joseph",
        "location": "Marina District",
        "avail_start": 10*60 + 45,   # 10:45
        "avail_end": 15*60,          # 15:00
        "min_duration": 90
    },
    {
        "person": "Ashley",
        "location": "Richmond District",
        "avail_start": 9*60 + 45,    # 9:45
        "avail_end": 11*60 + 15,     # 11:15
        "min_duration": 45
    },
    {
        "person": "Patricia",
        "location": "Union Square",
        "avail_start": 16*60 + 30,   # 16:30
        "avail_end": 20*60,          # 20:00
        "min_duration": 120
    },
    {
        "person": "Karen",
        "location": "Sunset District",
        "avail_start": 16*60 + 30,   # 16:30
        "avail_end": 22*60,          # 22:00
        "min_duration": 105
    },
]

# Global variable to keep track of the best itinerary (max number of meetings)
best_itinerary = []

# Backtracking search for the optimal meeting schedule
def search(current_time, current_location, remaining_meetings, itinerary):
    global best_itinerary
    # Update best itinerary if this itinerary has more meetings
    if len(itinerary) > len(best_itinerary):
        best_itinerary = itinerary.copy()
    
    # Try scheduling each remaining meeting
    for i, meeting in enumerate(remaining_meetings):
        # Get travel time from current_location to meeting location.
        key = (current_location, meeting["location"])
        if key not in travel_times:
            continue
        travel_time = travel_times[key]
        arrival_time = current_time + travel_time
        # Meeting can only start when both you have arrived and the friend is available.
        meeting_start = max(arrival_time, meeting["avail_start"])
        meeting_end = meeting_start + meeting["min_duration"]
        # Check if meeting can finish before friend's availability ends.
        if meeting_end <= meeting["avail_end"]:
            # Add meeting to itinerary
            meeting_record = {
                "action": "meet",
                "location": meeting["location"],
                "person": meeting["person"],
                "start_time": minutes_to_time_str(meeting_start),
                "end_time": minutes_to_time_str(meeting_end)
            }
            new_itinerary = itinerary + [meeting_record]
            # Recurse with the updated state; remove this meeting from remaining.
            new_remaining = remaining_meetings[:i] + remaining_meetings[i+1:]
            search(meeting_end, meeting["location"], new_remaining, new_itinerary)

def main():
    # Starting point: Financial District at 9:00 (9*60 minutes)
    start_time = 9 * 60  # 9:00 in minutes
    start_location = "Financial District"
    
    # Start recursive search
    search(start_time, start_location, meeting_constraints, [])
    
    # Create output dictionary following the required JSON structure.
    output = {"itinerary": best_itinerary}
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()