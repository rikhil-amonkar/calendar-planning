"""SOLUTION:"""
import json
from dataclasses import dataclass
from typing import List, Dict, Tuple, Optional

# -----------------------------
# Input parameters (editable)
# -----------------------------

ARRIVAL_LOCATION = "Russian Hill"
ARRIVAL_TIME_STR = "9:00"

TRAVEL_MINUTES: Dict[Tuple[str, str], int] = {
    ("Russian Hill", "Richmond District"): 14,
    ("Richmond District", "Russian Hill"): 13,
}

MIN_MEET_MINUTES = 45

FRIENDS_DATA = [
    {
        "name": "Barbara",
        "location": "Richmond District",
        "available_start": "13:15",
        "available_end": "18:15",
        "min_meet": MIN_MEET_MINUTES,
    }
]

# -----------------------------
# Utilities
# -----------------------------

def parse_time(t: str) -> int:
    h, m = t.split(":")
    return int(h) * 60 + int(m)

def fmt_time(minutes: int) -> str:
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

def travel_time(a: str, b: str) -> Optional[int]:
    return TRAVEL_MINUTES.get((a, b), None)

# -----------------------------
# Data classes
# -----------------------------

@dataclass
class Friend:
    name: str
    location: str
    available_start: int
    available_end: int
    min_meet: int

@dataclass
class MeetingOption:
    friend: Friend
    start: int
    end: int
    depart_time: int
    arrival_time: int
    wait_minutes: int
    travel_minutes: int

# -----------------------------
# Core scheduling logic
# -----------------------------

def enumerate_meeting_options_from_start(start_loc: str, start_time: int, friend: Friend) -> List[MeetingOption]:
    ttime = travel_time(start_loc, friend.location)
    if ttime is None:
        return []

    # Earliest we can arrive if we leave immediately
    earliest_arrival = start_time + ttime

    # Meeting can start no earlier than both the friend's available start and our earliest feasible arrival
    window_start = max(friend.available_start, earliest_arrival)
    window_end = friend.available_end

    if window_start + friend.min_meet > window_end:
        return []  # impossible to meet minimum duration

    options: List[MeetingOption] = []

    # Consider each feasible minute start time for the meeting
    for t in range(window_start, window_end - friend.min_meet + 1):
        # Choose depart time to arrive just-in-time (or later if we can't depart earlier than start_time)
        depart_time = max(start_time, t - ttime)
        arrival = depart_time + ttime

        # If arrival is after meeting start, this start time is not feasible
        if arrival > t:
            continue

        wait = t - arrival
        end = t + friend.min_meet

        options.append(
            MeetingOption(
                friend=friend,
                start=t,
                end=end,
                depart_time=depart_time,
                arrival_time=arrival,
                wait_minutes=wait,
                travel_minutes=ttime,
            )
        )

    return options

def choose_best_meeting(options: List[MeetingOption]) -> Optional[MeetingOption]:
    if not options:
        return None

    # Objective:
    # - maximize number of friends met (always 1 here)
    # Tie-breakers to choose the most "efficient" schedule:
    # 1) earliest end time (keeps rest of day open)
    # 2) minimal waiting + travel before the meeting
    # 3) earliest start time
    def key(opt: MeetingOption):
        return (
            opt.end,                      # minimize meeting end time
            opt.wait_minutes + opt.travel_minutes,  # minimize time overhead
            opt.start                     # minimize meeting start time
        )

    return min(options, key=key)

def compute_itinerary() -> List[Dict]:
    start_time = parse_time(ARRIVAL_TIME_STR)

    friends: List[Friend] = [
        Friend(
            name=f["name"],
            location=f["location"],
            available_start=parse_time(f["available_start"]),
            available_end=parse_time(f["available_end"]),
            min_meet=f["min_meet"],
        )
        for f in FRIENDS_DATA
    ]

    # Since only one friend is provided, we enumerate feasible meeting options for that friend
    best_overall: Optional[MeetingOption] = None

    for fr in friends:
        options = enumerate_meeting_options_from_start(ARRIVAL_LOCATION, start_time, fr)
        candidate = choose_best_meeting(options)
        if candidate:
            # Since all schedules meet exactly one friend, we pick the best by the same key
            if best_overall is None:
                best_overall = candidate
            else:
                def key(opt: MeetingOption):
                    return (
                        opt.end,
                        opt.wait_minutes + opt.travel_minutes,
                        opt.start
                    )
                if key(candidate) < key(best_overall):
                    best_overall = candidate

    itinerary: List[Dict] = []
    if best_overall:
        itinerary.append({
            "action": "meet",
            "location": best_overall.friend.location,
            "person": best_overall.friend.name,
            "start_time": fmt_time(best_overall.start),
            "end_time": fmt_time(best_overall.end),
        })
    return itinerary

# -----------------------------
# Main
# -----------------------------

if __name__ == "__main__":
    itinerary = compute_itinerary()
    result = {"itinerary": itinerary}
    print(json.dumps(result, ensure_ascii=False))