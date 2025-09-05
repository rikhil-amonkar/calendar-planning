import json
from dataclasses import dataclass
from typing import List, Tuple, Optional

# Input parameters (can be modified as needed)
arrival_location = "Nob Hill"
arrival_time_str = "9:00"  # 24-hour format without leading zeros
travel_times = {
    ("Nob Hill", "Presidio"): 17,
    ("Presidio", "Nob Hill"): 18,
}

# Friend constraints
friends = [
    {
        "name": "Robert",
        "location": "Presidio",
        "available_start": "11:15",
        "available_end": "17:45",
        "min_meeting_minutes": 120,
    }
]

# Utility functions
def parse_time(t: str) -> int:
    # t is like "9:00" or "13:30"
    parts = t.strip().split(":")
    h = int(parts[0])
    m = int(parts[1])
    return h * 60 + m

def fmt_time(minutes: int) -> str:
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

@dataclass
class ScheduleOption:
    num_people_met: int
    total_meeting_minutes: int
    total_waiting_minutes: int
    itinerary: List[dict]

def evaluate_schedule_for_single_friend(
    start_loc: str,
    day_start_min: int,
    travel_map: dict,
    friend: dict
) -> Optional[ScheduleOption]:
    # Extract friend parameters
    friend_loc = friend["location"]
    available_start = parse_time(friend["available_start"])
    available_end = parse_time(friend["available_end"])
    min_meeting = int(friend["min_meeting_minutes"])

    # Ensure travel exists
    if (start_loc, friend_loc) not in travel_map:
        return None

    travel_time = travel_map[(start_loc, friend_loc)]

    # Enumerate possible departure minutes from arrival time until the latest feasible
    # Latest departure to still allow minimum meeting time:
    latest_meeting_start = available_end - min_meeting
    latest_depart = latest_meeting_start - travel_time

    # If latest_depart is earlier than day start, still we can only depart at day start
    dep_start = day_start_min
    dep_end = max(day_start_min, latest_depart)

    best_option: Optional[ScheduleOption] = None

    for dep in range(dep_start, dep_end + 1):
        arrival = dep + travel_time
        # Meeting starts when both are present
        meet_start = max(arrival, available_start)
        # If meeting starts after availability ends, not feasible
        if meet_start >= available_end:
            continue

        # Meeting duration: maximize time with friend (until friend's end)
        meet_end = available_end
        duration = meet_end - meet_start

        if duration < min_meeting:
            continue

        waiting = max(0, available_start - arrival)

        itinerary = [
            {
                "action": "meet",
                "location": friend_loc,
                "person": friend["name"],
                "start_time": fmt_time(meet_start),
                "end_time": fmt_time(meet_end),
            }
        ]

        option = ScheduleOption(
            num_people_met=1,
            total_meeting_minutes=duration,
            total_waiting_minutes=waiting,
            itinerary=itinerary,
        )

        # Select best by:
        # 1) Maximize number of people met
        # 2) Maximize total meeting minutes
        # 3) Minimize waiting time
        # 4) Earliest start time (optional tiebreaker)
        def better(a: ScheduleOption, b: ScheduleOption) -> bool:
            if a.num_people_met != b.num_people_met:
                return a.num_people_met > b.num_people_met
            if a.total_meeting_minutes != b.total_meeting_minutes:
                return a.total_meeting_minutes > b.total_meeting_minutes
            if a.total_waiting_minutes != b.total_waiting_minutes:
                return a.total_waiting_minutes < b.total_waiting_minutes
            # Tiebreaker by earlier start time
            a_start = parse_time(a.itinerary[0]["start_time"])
            b_start = parse_time(b.itinerary[0]["start_time"])
            return a_start < b_start

        if best_option is None or better(option, best_option):
            best_option = option

    return best_option

def plan_day():
    day_start_min = parse_time(arrival_time_str)

    # Since only one friend is provided, we compute the best feasible schedule for Robert
    best_overall: Optional[ScheduleOption] = None

    for friend in friends:
        option = evaluate_schedule_for_single_friend(
            start_loc=arrival_location,
            day_start_min=day_start_min,
            travel_map=travel_times,
            friend=friend,
        )
        # Choose the plan that meets the most friends; since there's only one friend, this simplifies
        if option is None:
            continue
        if best_overall is None:
            best_overall = option
        else:
            # Compare options (though only one friend exists here)
            def better(a: ScheduleOption, b: ScheduleOption) -> bool:
                if a.num_people_met != b.num_people_met:
                    return a.num_people_met > b.num_people_met
                if a.total_meeting_minutes != b.total_meeting_minutes:
                    return a.total_meeting_minutes > b.total_meeting_minutes
                if a.total_waiting_minutes != b.total_waiting_minutes:
                    return a.total_waiting_minutes < b.total_waiting_minutes
                a_start = parse_time(a.itinerary[0]["start_time"])
                b_start = parse_time(b.itinerary[0]["start_time"])
                return a_start < b_start
            if better(option, best_overall):
                best_overall = option

    itinerary = best_overall.itinerary if best_overall else []
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = plan_day()
    print(json.dumps(result, ensure_ascii=False))