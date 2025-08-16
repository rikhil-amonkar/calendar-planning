from z3 import *
import json

# Helper function to convert minutes (since midnight) to "HH:MM" string.
def minutes_to_str(m):
    h = m // 60
    mi = m % 60
    return f"{h:02d}:{mi:02d}"

def main():
    # Create an Optimize solver so we can maximize number of meetings attended.
    opt = Optimize()

    # Our day is modeled in minutes after midnight.
    # We start at Bayview at 09:00 (9*60 = 540 minutes).
    start_from = 540

    # List of friends and their meeting details.
    # Each friend has: location, available start (in minutes), available end (in minutes) and minimum meeting duration.
    # Times are given in minutes from midnight.
    details = {
        "Brian":    {"location": "North Beach",        "avail_start": 780,  "avail_end": 1140, "duration": 90},   # 13:00 - 19:00
        "Richard":  {"location": "Fisherman's Wharf",  "avail_start": 660,  "avail_end": 765,  "duration": 60},   # 11:00 - 12:45
        "Ashley":   {"location": "Haight-Ashbury",     "avail_start": 900,  "avail_end": 1230, "duration": 90},   # 15:00 - 20:30
        "Elizabeth":{"location": "Nob Hill",           "avail_start": 705,  "avail_end": 1110, "duration": 75},   # 11:45 - 18:30
        "Jessica":  {"location": "Golden Gate Park",   "avail_start": 1200, "avail_end": 1305, "duration": 105},  # 20:00 - 21:45
        "Deborah":  {"location": "Union Square",       "avail_start": 1050, "avail_end": 1320, "duration": 60},   # 17:30 - 22:00
        "Kimberly": {"location": "Alamo Square",       "avail_start": 1050, "avail_end": 1275, "duration": 45},   # 17:30 - 21:15
        "Matthew":  {"location": "Presidio",           "avail_start": 495,  "avail_end": 540,  "duration": 15},   # 8:15 - 9:00
        "Kenneth":  {"location": "Chinatown",          "avail_start": 825,  "avail_end": 1170, "duration": 105},  # 13:45 - 19:30
        "Anthony":  {"location": "Pacific Heights",    "avail_start": 855,  "avail_end": 960,  "duration": 30}    # 14:15 - 16:00
    }
    friends = list(details.keys())

    # Travel time dictionary between places (in minutes).
    # Each entry travel_times[A][B] is the travel time from location A to location B.
    travel_times = {
        "Bayview": {
            "North Beach": 22, "Fisherman's Wharf": 25, "Haight-Ashbury": 19,
            "Nob Hill": 20, "Golden Gate Park": 22, "Union Square": 18,
            "Alamo Square": 16, "Presidio": 32, "Chinatown": 19, "Pacific Heights": 23
        },
        "North Beach": {
            "Bayview": 25, "Fisherman's Wharf": 5, "Haight-Ashbury": 18,
            "Nob Hill": 7, "Golden Gate Park": 22, "Union Square": 7,
            "Alamo Square": 16, "Presidio": 17, "Chinatown": 6, "Pacific Heights": 8
        },
        "Fisherman's Wharf": {
            "Bayview": 26, "North Beach": 6, "Haight-Ashbury": 23,
            "Nob Hill": 11, "Golden Gate Park": 25, "Union Square": 13,
            "Alamo Square": 21, "Presidio": 17, "Chinatown": 12, "Pacific Heights": 12
        },
        "Haight-Ashbury": {
            "Bayview": 18, "North Beach": 19, "Fisherman's Wharf": 23,
            "Nob Hill": 15, "Golden Gate Park": 7, "Union Square": 19,
            "Alamo Square": 5, "Presidio": 15, "Chinatown": 19, "Pacific Heights": 12
        },
        "Nob Hill": {
            "Bayview": 19, "North Beach": 8, "Fisherman's Wharf": 10,
            "Haight-Ashbury": 13, "Golden Gate Park": 17, "Union Square": 7,
            "Alamo Square": 11, "Presidio": 17, "Chinatown": 6, "Pacific Heights": 8
        },
        "Golden Gate Park": {
            "Bayview": 23, "North Beach": 23, "Fisherman's Wharf": 24,
            "Haight-Ashbury": 7, "Nob Hill": 20, "Union Square": 22,
            "Alamo Square": 9, "Presidio": 11, "Chinatown": 23, "Pacific Heights": 16
        },
        "Union Square": {
            "Bayview": 15, "North Beach": 10, "Fisherman's Wharf": 15,
            "Haight-Ashbury": 18, "Nob Hill": 9, "Golden Gate Park": 22,
            "Alamo Square": 15, "Presidio": 24, "Chinatown": 7, "Pacific Heights": 15
        },
        "Alamo Square": {
            "Bayview": 16, "North Beach": 15, "Fisherman's Wharf": 19,
            "Haight-Ashbury": 5, "Nob Hill": 11, "Golden Gate Park": 9,
            "Union Square": 14, "Presidio": 17, "Chinatown": 15, "Pacific Heights": 10
        },
        "Presidio": {
            "Bayview": 31, "North Beach": 18, "Fisherman's Wharf": 19,
            "Haight-Ashbury": 15, "Nob Hill": 18, "Golden Gate Park": 12,
            "Union Square": 22, "Alamo Square": 19, "Chinatown": 21, "Pacific Heights": 11
        },
        "Chinatown": {
            "Bayview": 20, "North Beach": 3, "Fisherman's Wharf": 8,
            "Haight-Ashbury": 19, "Nob Hill": 9, "Golden Gate Park": 23,
            "Union Square": 7, "Alamo Square": 17, "Presidio": 19, "Pacific Heights": 10
        },
        "Pacific Heights": {
            "Bayview": 22, "North Beach": 9, "Fisherman's Wharf": 13,
            "Haight-Ashbury": 11, "Nob Hill": 8, "Golden Gate Park": 15,
            "Union Square": 12, "Alamo Square": 10, "Presidio": 11, "Chinatown": 11
        }
    }

    # Create Z3 variables:
    # For each friend, we create an integer variable s_{friend} representing the meeting start time (in minutes).
    # And a Boolean variable attend_{friend} indicating whether you schedule a meeting with that friend.
    s = {}
    attend = {}
    for friend in friends:
        s[friend] = Int("s_" + friend)
        attend[friend] = Bool("attend_" + friend)

        # Compute the lower bound for the meeting start:
        # It must be no earlier than the friend’s availability and also no earlier than when you can get there from Bayview.
        friend_lower = details[friend]["avail_start"]
        travel_from_bayview = travel_times["Bayview"][details[friend]["location"]]
        lower_bound = max(friend_lower, start_from + travel_from_bayview)
        # If meeting is scheduled (attend==True), then s[friend] >= lower_bound.
        opt.add(Or(Not(attend[friend]), s[friend] >= lower_bound))

        # Also, if you meet the friend, you must finish by the friend’s available end.
        # That is, s[friend] + meeting_duration <= avail_end.
        opt.add(Or(Not(attend[friend]), s[friend] <= details[friend]["avail_end"] - details[friend]["duration"]))
        
        # Restrict all meeting start times to be within a reasonable day (0 to 1440 minutes).
        opt.add(s[friend] >= 0, s[friend] <= 1440)

    # Add ordering constraints between every pair of friends.
    # If both meetings are scheduled then one must occur before the other with sufficient travel time in between.
    for i in range(len(friends)):
        for j in range(i+1, len(friends)):
            f_i = friends[i]
            f_j = friends[j]
            loc_i = details[f_i]["location"]
            loc_j = details[f_j]["location"]
            dur_i = details[f_i]["duration"]
            dur_j = details[f_j]["duration"]
            travel_ij = travel_times[loc_i][loc_j]
            travel_ji = travel_times[loc_j][loc_i]

            # If both f_i and f_j are attended then either:
            #   (s[f_i] + dur_i + travel from i to j) <= s[f_j]
            # or
            #   (s[f_j] + dur_j + travel from j to i) <= s[f_i]
            opt.add(
                Or(
                    Not(And(attend[f_i], attend[f_j])),
                    s[f_i] + dur_i + travel_ij <= s[f_j],
                    s[f_j] + dur_j + travel_ji <= s[f_i]
                )
            )

    # Our objective is to maximize the total number of meetings (friends attended).
    total_meetings = Sum([If(attend[friend], 1, 0) for friend in friends])
    opt.maximize(total_meetings)

    # Check for solution.
    if opt.check() == sat:
        m = opt.model()
        scheduled = []
        # Gather meetings for friends which are scheduled (attend==True)
        for friend in friends:
            if is_true(m.evaluate(attend[friend])):
                start_time = m.evaluate(s[friend]).as_long()
                end_time = start_time + details[friend]["duration"]
                scheduled.append((start_time, friend, end_time))
        # Sort the meetings in increasing order of start time.
        scheduled.sort(key=lambda tup: tup[0])
        
        itinerary = []
        for st, friend, et in scheduled:
            itinerary.append({
                "action": "meet",
                "person": friend,
                "start_time": minutes_to_str(st),
                "end_time": minutes_to_str(et)
            })
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print("No solution found")

if __name__ == "__main__":
    main()