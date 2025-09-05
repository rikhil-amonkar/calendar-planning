import json
from dataclasses import dataclass
from typing import Dict, Tuple, Optional, List

# Helper functions for time parsing/formatting
def parse_time(t: str) -> int:
    h, m = map(int, t.split(":"))
    return h * 60 + m

def fmt_time(minutes: int) -> str:
    h = minutes // 60
    m = minutes % 60
    return f"{h}:{m:02d}"

@dataclass
class Friend:
    name: str
    location: str
    availability_start: str
    availability_end: str
    min_meet_minutes: int

class Planner:
    def __init__(self,
                 start_location: str,
                 arrival_time_at_start: str,
                 travel_times: Dict[Tuple[str, str], int],
                 friends: List[Friend]):
        self.start_location = start_location
        self.start_time = parse_time(arrival_time_at_start)
        self.travel_times = travel_times
        self.friends = friends

    def travel_time(self, a: str, b: str) -> Optional[int]:
        return self.travel_times.get((a, b), None)

    def plan(self) -> Dict:
        itinerary = []

        # Goal: maximize number of friends met. Here, we only have Daniel.
        # We'll compute for each friend whether we can meet them respecting travel and time windows,
        # and choose the plan that meets the most friends. With a single friend, this reduces to:
        # try to meet Daniel for at least his minimum required duration.

        # Since there is only one friend, we attempt to meet them optimally.
        best_plan = None  # store dict with details if feasible

        for friend in self.friends:
            avail_start = parse_time(friend.availability_start)
            avail_end = parse_time(friend.availability_end)
            tt = self.travel_time(self.start_location, friend.location)
            if tt is None:
                continue  # cannot travel, skip

            # We consider all possible departure times from start_location (by the minute)
            # and compute the actual overlap with the friend's availability window.
            # Objective: achieve at least min_meet_minutes; among feasible options,
            # choose the one with the largest meeting time (then latest departure to minimize waiting).
            feasible_option = None
            max_meet = -1
            best_latest_depart = None

            # We can depart anytime from arrival at start location up to the last departure that could still arrive before friend's end.
            last_possible_depart = avail_end - tt
            for depart in range(self.start_time, max(self.start_time, last_possible_depart) + 1):
                arrive = depart + tt
                # If we arrive after the friend's availability ends, no meeting possible.
                if arrive >= avail_end:
                    continue
                meet_start = max(arrive, avail_start)
                meet_end = avail_end
                if meet_start >= meet_end:
                    continue
                meet_len = meet_end - meet_start
                if meet_len >= friend.min_meet_minutes:
                    # Feasible. Track the best according to our objective.
                    # Primary: maximize meeting length; Secondary: maximize depart (leave as late as possible).
                    if meet_len > max_meet or (meet_len == max_meet and (best_latest_depart is None or depart > best_latest_depart)):
                        max_meet = meet_len
                        best_latest_depart = depart
                        feasible_option = {
                            "friend": friend.name,
                            "location": friend.location,
                            "meet_start": meet_start,
                            "meet_end": meet_end,
                            "depart_time": depart,
                            "arrival_time": arrive,
                        }

            if feasible_option:
                # With only one friend, this is our best plan.
                best_plan = feasible_option
                # Since we are maximizing friends met and we have only one, we can break.
                break

        if best_plan:
            itinerary.append({
                "action": "meet",
                "location": best_plan["location"],
                "person": self.friends[0].name,
                "start_time": fmt_time(best_plan["meet_start"]),
                "end_time": fmt_time(best_plan["meet_end"])
            })

        return {"itinerary": itinerary}

def main():
    # Input parameters
    start_location = "Russian Hill"
    arrival_time_at_start = "9:00"

    # Travel times (minutes)
    travel_times = {
        ("Russian Hill", "Richmond District"): 14,
        ("Richmond District", "Russian Hill"): 13
    }

    # Friends and their constraints
    friends = [
        Friend(
            name="Daniel",
            location="Richmond District",
            availability_start="19:00",
            availability_end="20:15",
            min_meet_minutes=75
        )
    ]

    planner = Planner(start_location, arrival_time_at_start, travel_times, friends)
    result = planner.plan()
    print(json.dumps(result, ensure_ascii=False))

if __name__ == "__main__":
    main()