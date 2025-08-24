import json
from dataclasses import dataclass
from typing import Dict, List, Optional, Tuple

# Helper functions for time formatting
def to_minutes(h: int, m: int) -> int:
    return h * 60 + m

def minutes_to_str(t: int) -> str:
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

@dataclass
class Person:
    name: str
    location: str
    start: int  # minutes since midnight
    end: int    # minutes since midnight
    min_dur: int  # minutes

@dataclass
class Meeting:
    person: str
    location: str
    start: int
    end: int

# Define locations
locations = [
    "Embarcadero",
    "Bayview",
    "Chinatown",
    "Alamo Square",
    "Nob Hill",
    "Presidio",
    "Union Square",
    "The Castro",
    "North Beach",
    "Fisherman's Wharf",
    "Marina District",
]

# Directed travel times in minutes
T: Dict[str, Dict[str, int]] = {loc: {} for loc in locations}

# Populate travel times (directed)
T["Embarcadero"].update({
    "Bayview": 21, "Chinatown": 7, "Alamo Square": 19, "Nob Hill": 10, "Presidio": 20,
    "Union Square": 10, "The Castro": 25, "North Beach": 5, "Fisherman's Wharf": 6, "Marina District": 12
})
T["Bayview"].update({
    "Embarcadero": 19, "Chinatown": 19, "Alamo Square": 16, "Nob Hill": 20, "Presidio": 32,
    "Union Square": 18, "The Castro": 19, "North Beach": 22, "Fisherman's Wharf": 25, "Marina District": 27
})
T["Chinatown"].update({
    "Embarcadero": 5, "Bayview": 20, "Alamo Square": 17, "Nob Hill": 9, "Presidio": 19,
    "Union Square": 7, "The Castro": 22, "North Beach": 3, "Fisherman's Wharf": 8, "Marina District": 12
})
T["Alamo Square"].update({
    "Embarcadero": 16, "Bayview": 16, "Chinatown": 15, "Nob Hill": 11, "Presidio": 17,
    "Union Square": 14, "The Castro": 8, "North Beach": 15, "Fisherman's Wharf": 19, "Marina District": 15
})
T["Nob Hill"].update({
    "Embarcadero": 9, "Bayview": 19, "Chinatown": 6, "Alamo Square": 11, "Presidio": 17,
    "Union Square": 7, "The Castro": 17, "North Beach": 8, "Fisherman's Wharf": 10, "Marina District": 11
})
T["Presidio"].update({
    "Embarcadero": 20, "Bayview": 31, "Chinatown": 21, "Alamo Square": 19, "Nob Hill": 18,
    "Union Square": 22, "The Castro": 21, "North Beach": 18, "Fisherman's Wharf": 19, "Marina District": 11
})
T["Union Square"].update({
    "Embarcadero": 11, "Bayview": 15, "Chinatown": 7, "Alamo Square": 15, "Nob Hill": 9,
    "Presidio": 24, "The Castro": 17, "North Beach": 10, "Fisherman's Wharf": 15, "Marina District": 18
})
T["The Castro"].update({
    "Embarcadero": 22, "Bayview": 19, "Chinatown": 22, "Alamo Square": 8, "Nob Hill": 16,
    "Presidio": 20, "Union Square": 19, "North Beach": 20, "Fisherman's Wharf": 24, "Marina District": 21
})
T["North Beach"].update({
    "Embarcadero": 6, "Bayview": 25, "Chinatown": 6, "Alamo Square": 16, "Nob Hill": 7,
    "Presidio": 17, "Union Square": 7, "The Castro": 23, "Fisherman's Wharf": 5, "Marina District": 9
})
T["Fisherman's Wharf"].update({
    "Embarcadero": 8, "Bayview": 26, "Chinatown": 12, "Alamo Square": 21, "Nob Hill": 11,
    "Presidio": 17, "Union Square": 13, "The Castro": 27, "North Beach": 6, "Marina District": 9
})
T["Marina District"].update({
    "Embarcadero": 14, "Bayview": 27, "Chinatown": 15, "Alamo Square": 15, "Nob Hill": 12,
    "Presidio": 10, "Union Square": 16, "The Castro": 22, "North Beach": 11, "Fisherman's Wharf": 10
})

# People and constraints
people: Dict[str, Person] = {
    "Matthew":   Person("Matthew", "Bayview",           to_minutes(19,15), to_minutes(22,0), 120),
    "Karen":     Person("Karen",   "Chinatown",         to_minutes(19,15), to_minutes(21,15), 90),
    "Sarah":     Person("Sarah",   "Alamo Square",      to_minutes(20,0),  to_minutes(21,45), 105),
    "Jessica":   Person("Jessica", "Nob Hill",          to_minutes(16,30), to_minutes(18,45), 120),
    "Stephanie": Person("Stephanie","Presidio",         to_minutes(7,30),  to_minutes(10,15), 60),
    "Mary":      Person("Mary",    "Union Square",      to_minutes(16,45), to_minutes(21,30), 60),
    "Charles":   Person("Charles", "The Castro",        to_minutes(16,30), to_minutes(22,0), 105),
    "Nancy":     Person("Nancy",   "North Beach",       to_minutes(14,45), to_minutes(20,0), 15),
    "Thomas":    Person("Thomas",  "Fisherman's Wharf", to_minutes(13,30), to_minutes(19,0), 30),
    "Brian":     Person("Brian",   "Marina District",   to_minutes(12,15), to_minutes(18,0), 60),
}

START_LOCATION = "Embarcadero"
START_TIME = to_minutes(9, 0)

# Check travel time availability
def travel_time(src: str, dst: str) -> Optional[int]:
    if src == dst:
        return 0
    return T.get(src, {}).get(dst, None)

# Compute earliest feasible meeting interval for a person from a given state
def earliest_feasible(current_loc: str, current_time: int, p: Person) -> Optional[Tuple[int, int, int]]:
    tt = travel_time(current_loc, p.location)
    if tt is None:
        return None
    arrive = current_time + tt
    start = max(arrive, p.start)
    end = start + p.min_dur
    if end <= p.end:
        return (start, end, tt)
    return None

# DFS search to maximize number of meetings
class BestSolution:
    def __init__(self):
        self.schedule: List[Meeting] = []
        self.count = 0
        self.total_meeting_time = 0
        self.end_time = START_TIME
        self.total_travel = 0

    def better_than(self, other: 'BestSolution') -> bool:
        # Maximize number of meetings
        if self.count != other.count:
            return self.count > other.count
        # Then maximize total meeting time
        if self.total_meeting_time != other.total_meeting_time:
            return self.total_meeting_time > other.total_meeting_time
        # Then minimize end time
        if self.end_time != other.end_time:
            return self.end_time < other.end_time
        # Then minimize total travel
        return self.total_travel < other.total_travel

def dfs(current_loc: str, current_time: int, remaining: List[str], current_schedule: List[Meeting], current_travel: int, best: BestSolution):
    # Prune if even taking all remaining we can't beat current best
    potential_max = len(current_schedule) + len(remaining)
    if potential_max < best.count:
        return

    improved = False
    # Try each remaining person as next
    for name in list(remaining):
        p = people[name]
        feas = earliest_feasible(current_loc, current_time, p)
        if feas is None:
            continue
        start, end, tt = feas
        # Build next state
        next_schedule = current_schedule + [Meeting(p.name, p.location, start, end)]
        next_remaining = remaining.copy()
        next_remaining.remove(name)
        # Recurse from end time and new location
        dfs(p.location, end, next_remaining, next_schedule, current_travel + tt, best)
        improved = True

    # If no further improvements or branches processed, evaluate current schedule
    if not improved:
        sol = BestSolution()
        sol.schedule = current_schedule
        sol.count = len(current_schedule)
        sol.total_meeting_time = sum(m.end - m.start for m in current_schedule)
        sol.end_time = current_time
        sol.total_travel = current_travel
        if sol.better_than(best):
            best.schedule = sol.schedule
            best.count = sol.count
            best.total_meeting_time = sol.total_meeting_time
            best.end_time = sol.end_time
            best.total_travel = sol.total_travel

def compute_optimal_schedule():
    remaining = list(people.keys())
    best = BestSolution()
    dfs(START_LOCATION, START_TIME, remaining, [], 0, best)
    return best.schedule

def main():
    schedule = compute_optimal_schedule()
    itinerary = []
    for m in schedule:
        itinerary.append({
            "action": "meet",
            "location": m.location,
            "person": m.person,
            "start_time": minutes_to_str(m.start),
            "end_time": minutes_to_str(m.end),
        })
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False))

if __name__ == "__main__":
    main()