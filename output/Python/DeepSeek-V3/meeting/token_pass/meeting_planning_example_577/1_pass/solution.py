import json
import itertools
from typing import List, Dict, Tuple, Optional

def time_to_min(t: str) -> int:
    """Convert 'H:MM' or 'HH:MM' to minutes since midnight."""
    h, m = map(int, t.split(':'))
    return h * 60 + m

def min_to_time(m: int) -> str:
    """Convert minutes since midnight to 'H:MM' (no leading zero on hour)."""
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

# Travel times matrix (in minutes)
# Keys: (from, to)
travel = {
    ('Haight-Ashbury', 'Russian Hill'): 17,
    ('Haight-Ashbury', 'Fisherman\'s Wharf'): 23,
    ('Haight-Ashbury', 'Nob Hill'): 15,
    ('Haight-Ashbury', 'Golden Gate Park'): 7,
    ('Haight-Ashbury', 'Alamo Square'): 5,
    ('Haight-Ashbury', 'Pacific Heights'): 12,
    ('Russian Hill', 'Haight-Ashbury'): 17,
    ('Russian Hill', 'Fisherman\'s Wharf'): 7,
    ('Russian Hill', 'Nob Hill'): 5,
    ('Russian Hill', 'Golden Gate Park'): 21,
    ('Russian Hill', 'Alamo Square'): 15,
    ('Russian Hill', 'Pacific Heights'): 7,
    ('Fisherman\'s Wharf', 'Haight-Ashbury'): 22,
    ('Fisherman\'s Wharf', 'Russian Hill'): 7,
    ('Fisherman\'s Wharf', 'Nob Hill'): 11,
    ('Fisherman\'s Wharf', 'Golden Gate Park'): 25,
    ('Fisherman\'s Wharf', 'Alamo Square'): 20,
    ('Fisherman\'s Wharf', 'Pacific Heights'): 12,
    ('Nob Hill', 'Haight-Ashbury'): 13,
    ('Nob Hill', 'Russian Hill'): 5,
    ('Nob Hill', 'Fisherman\'s Wharf'): 11,
    ('Nob Hill', 'Golden Gate Park'): 17,
    ('Nob Hill', 'Alamo Square'): 11,
    ('Nob Hill', 'Pacific Heights'): 8,
    ('Golden Gate Park', 'Haight-Ashbury'): 7,
    ('Golden Gate Park', 'Russian Hill'): 19,
    ('Golden Gate Park', 'Fisherman\'s Wharf'): 24,
    ('Golden Gate Park', 'Nob Hill'): 20,
    ('Golden Gate Park', 'Alamo Square'): 10,
    ('Golden Gate Park', 'Pacific Heights'): 16,
    ('Alamo Square', 'Haight-Ashbury'): 5,
    ('Alamo Square', 'Russian Hill'): 13,
    ('Alamo Square', 'Fisherman\'s Wharf'): 19,
    ('Alamo Square', 'Nob Hill'): 11,
    ('Alamo Square', 'Golden Gate Park'): 9,
    ('Alamo Square', 'Pacific Heights'): 10,
    ('Pacific Heights', 'Haight-Ashbury'): 11,
    ('Pacific Heights', 'Russian Hill'): 7,
    ('Pacific Heights', 'Fisherman\'s Wharf'): 13,
    ('Pacific Heights', 'Nob Hill'): 8,
    ('Pacific Heights', 'Golden Gate Park'): 15,
    ('Pacific Heights', 'Alamo Square'): 10,
}

# Friend data: name, location, window start, window end, min_duration (all in minutes)
friends = [
    ('Stephanie', 'Russian Hill', time_to_min('20:00'), time_to_min('20:45'), 15),
    ('Kevin', 'Fisherman\'s Wharf', time_to_min('19:15'), time_to_min('21:45'), 75),
    ('Robert', 'Nob Hill', time_to_min('7:45'), time_to_min('10:30'), 90),
    ('Steven', 'Golden Gate Park', time_to_min('8:30'), time_to_min('17:00'), 75),
    ('Anthony', 'Alamo Square', time_to_min('7:45'), time_to_min('19:45'), 15),
    ('Sandra', 'Pacific Heights', time_to_min('14:45'), time_to_min('21:45'), 45),
]

# Start at Haight-Ashbury at 9:00
start_time = time_to_min('9:00')
start_loc = 'Haight-Ashbury'

def schedule_meeting(current_time: int, current_loc: str, friend_info: Tuple) -> Optional[Tuple[int, int, str]]:
    """Try to schedule meeting with friend.
    Returns (meet_start, meet_end, friend_location) if possible, else None."""
    name, loc, win_start, win_end, min_dur = friend_info
    travel_time = travel.get((current_loc, loc))
    if travel_time is None:
        travel_time = 0  # same location
    
    arrive = current_time + travel_time
    # Start meeting at max(arrive, win_start)
    meet_start = max(arrive, win_start)
    if meet_start + min_dur > win_end:
        return None  # cannot meet
    meet_end = meet_start + min_dur
    return (meet_start, meet_end, loc)

def evaluate_permutation(perm: List[Tuple]) -> Tuple[int, int, List[Tuple]]:
    """Return (num_met, total_social_time, itinerary_entries) for this permutation."""
    current_time = start_time
    current_loc = start_loc
    met = []
    total_social = 0
    itinerary = []
    
    for finfo in perm:
        res = schedule_meeting(current_time, current_loc, finfo)
        if res is None:
            return 0, 0, []  # this permutation fails
        meet_start, meet_end, loc = res
        name = finfo[0]
        itinerary.append(('meet', loc, name, meet_start, meet_end))
        total_social += (meet_end - meet_start)
        current_time = meet_end
        current_loc = loc
        met.append(finfo)
    
    return len(met), total_social, itinerary

def main():
    best_count = 0
    best_social = 0
    best_itinerary = []
    
    # Try all subsets (except empty) and all permutations
    friend_indices = list(range(len(friends)))
    for r in range(1, len(friends) + 1):
        for subset in itertools.combinations(friend_indices, r):
            for perm_indices in itertools.permutations(subset):
                perm = [friends[i] for i in perm_indices]
                count, social, itinerary = evaluate_permutation(perm)
                if count > best_count or (count == best_count and social > best_social):
                    best_count = count
                    best_social = social
                    best_itinerary = itinerary
    
    # Convert itinerary to required JSON format
    result = {"itinerary": []}
    for action, loc, person, start_min, end_min in best_itinerary:
        result["itinerary"].append({
            "action": "meet",
            "location": loc,
            "person": person,
            "start_time": min_to_time(start_min),
            "end_time": min_to_time(end_min)
        })
    
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()