"""SOLUTION:"""
import json

def to_minutes(tstr):
    h, m = map(int, tstr.split(":"))
    return h * 60 + m

def fmt_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}"

def compute_optimal_schedule():
    # Input variables (meeting constraints and travel times)
    start_location = "Golden Gate Park"
    arrival_time_str = "9:00"  # arrival at Golden Gate Park
    travel_minutes = {
        ("Golden Gate Park", "Chinatown"): 23,
        ("Chinatown", "Golden Gate Park"): 23,
    }
    friends = [
        {
            "name": "David",
            "location": "Chinatown",
            "available_start": "16:00",
            "available_end": "21:45",
            "min_meeting_minutes": 105
        }
    ]

    # Helper to get travel time between locations
    def travel_time(a, b):
        return travel_minutes.get((a, b), None)

    # Convert inputs to minutes
    current_loc = start_location
    arrival_time = to_minutes(arrival_time_str)

    best_plan = None  # (friends_met, total_meeting_minutes, -waiting_time, start, end, friend)
    best_itinerary = []

    for friend in friends:
        loc = friend["location"]
        t_travel = travel_time(current_loc, loc)
        if t_travel is None:
            continue  # cannot reach this friend

        # Earliest arrival at friend's location if departing as soon as possible
        earliest_arrival_at_friend = arrival_time + t_travel

        avail_start = to_minutes(friend["available_start"])
        avail_end = to_minutes(friend["available_end"])
        min_meet = friend["min_meeting_minutes"]

        # Feasible meeting window intersection
        meeting_window_start = max(avail_start, earliest_arrival_at_friend)
        meeting_window_end = avail_end

        if meeting_window_end - meeting_window_start < min_meet:
            continue  # not enough time to meet the minimum

        # Consider various possible start/end times within the feasible window
        # Objective:
        # 1) Maximize number of friends met
        # 2) Maximize total meeting minutes
        # 3) Minimize waiting time (we can depart later from start to arrive just in time)
        # 4) Earliest start (as a tiebreaker)
        # We will model waiting time as 0 by aligning departure to arrive at meeting start.
        # Still, we enumerate to satisfy the "consider various schedules" requirement.
        candidate_best = None
        for meet_start in range(meeting_window_start, meeting_window_end - min_meet + 1):
            for meet_end in range(meet_start + min_meet, meeting_window_end + 1):
                # We can leave start location at (meet_start - t_travel) to arrive just in time.
                depart_time = meet_start - t_travel
                if depart_time < arrival_time:
                    # Cannot depart before arriving at the initial location
                    # In this case, we would arrive earlier and wait; compute waiting at friend's location
                    waiting = max(0, meet_start - earliest_arrival_at_friend)
                else:
                    # Depart later to arrive just in time; no waiting
                    waiting = 0

                friends_met = 1
                total_meeting_minutes = meet_end - meet_start
                score = (friends_met, total_meeting_minutes, -waiting, -meet_start)

                if candidate_best is None or score > candidate_best[0]:
                    candidate_best = (score, meet_start, meet_end)

        if candidate_best:
            score, meet_start, meet_end = candidate_best
            # Update global best (only one friend here, but keep generic)
            if best_plan is None or score > best_plan[0]:
                best_plan = (score, meet_start, meet_end, friend)

    if best_plan:
        _, meet_start, meet_end, friend = best_plan
        best_itinerary.append({
            "action": "meet",
            "location": friend["location"],
            "person": friend["name"],
            "start_time": fmt_time(meet_start),
            "end_time": fmt_time(meet_end)
        })

    result = {"itinerary": best_itinerary}
    return result

if __name__ == "__main__":
    plan = compute_optimal_schedule()
    print(json.dumps(plan, ensure_ascii=False))