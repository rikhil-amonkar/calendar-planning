import json
from dataclasses import dataclass
from typing import List, Dict, Any, Optional, Tuple

# -----------------------------
# Input Parameters (editable)
# -----------------------------
start_location = "Nob Hill"
day_start_time_str = "9:00"  # arrival at Nob Hill

# Friend info
friends = [
    {
        "name": "Robert",
        "location": "Presidio",
        "available_start": "11:15",
        "available_end": "17:45",
        "min_meeting_minutes": 120
    }
]

# Travel times in minutes (directed)
travel_minutes = {
    ("Nob Hill", "Presidio"): 17,
    ("Presidio", "Nob Hill"): 18
}

# -----------------------------
# Utilities
# -----------------------------
def time_to_min(t: str) -> int:
    """Convert 'H:MM' 24-hour string to minutes from midnight."""
    h, m = map(int, t.split(":"))
    return h * 60 + m

def min_to_time(m: int) -> str:
    """Convert minutes from midnight to 'H:MM' 24-hour string without leading zero on hour."""
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

@dataclass
class Meeting:
    person: str
    location: str
    start: int
    end: int

@dataclass
class CandidatePlan:
    meetings: List[Meeting]
    score: Tuple[int, int, int, int]  # (-count, -total_meet_minutes, waiting_time, -last_depart_time)

# -----------------------------
# Core Scheduling Logic
# -----------------------------
def compute_optimal_schedule() -> Dict[str, Any]:
    # Initialize times
    day_start = time_to_min(day_start_time_str)

    # Prepare friend windows
    friend_windows = []
    for fr in friends:
        friend_windows.append({
            "name": fr["name"],
            "location": fr["location"],
            "start": time_to_min(fr["available_start"]),
            "end": time_to_min(fr["available_end"]),
            "min_minutes": fr["min_meeting_minutes"]
        })

    # Since there is only one friend, we still enumerate multiple feasible departure times
    # to "consider various different schedules" and then choose the best according to goals.
    candidates: List[CandidatePlan] = []

    # Helper to get travel time
    def get_travel(a: str, b: str) -> Optional[int]:
        return travel_minutes.get((a, b))

    # Starting at start_location at day_start
    current_loc = start_location

    for fr in friend_windows:
        to_friend = get_travel(current_loc, fr["location"])
        if to_friend is None:
            continue  # no path defined

        # Latest depart time that still allows minimum meeting duration
        latest_depart = fr["end"] - fr["min_minutes"] - to_friend

        # Enumerate departure times from arrival time onward up to latest feasible
        if latest_depart < day_start:
            continue  # cannot make minimum duration

        for depart in range(day_start, latest_depart + 1):
            arrive = depart + to_friend
            # Meeting can only start when friend is available and after arrival
            meet_start = max(arrive, fr["start"])
            meet_end = fr["end"]
            if meet_start >= meet_end:
                continue
            duration = meet_end - meet_start
            if duration < fr["min_minutes"]:
                continue

            # Waiting time is time from arrival until meeting start if arriving early
            waiting = max(0, fr["start"] - arrive)

            # Score:
            # Primary objective: maximize number of friends met (count)
            # Secondary: maximize total meeting time
            # Tertiary: minimize waiting time
            # Quaternary: prefer later departure among ties (to reduce idle time elsewhere)
            num_meetings = 1
            total_meet_minutes = duration
            score = (-num_meetings, -total_meet_minutes, waiting, -depart)

            meeting = Meeting(
                person=fr["name"],
                location=fr["location"],
                start=meet_start,
                end=meet_end
            )
            candidates.append(CandidatePlan(meetings=[meeting], score=score))

    # Choose best candidate
    if not candidates:
        itinerary: List[Dict[str, str]] = []
    else:
        best = min(candidates, key=lambda c: c.score)
        itinerary = []
        for m in best.meetings:
            itinerary.append({
                "action": "meet",
                "location": m.location,
                "person": m.person,
                "start_time": min_to_time(m.start),
                "end_time": min_to_time(m.end)
            })

    return {"itinerary": itinerary}

# -----------------------------
# Execute and Output JSON
# -----------------------------
if __name__ == "__main__":
    result = compute_optimal_schedule()
    print(json.dumps(result, ensure_ascii=False))