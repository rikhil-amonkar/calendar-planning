# SOLUTION:
import json
from functools import lru_cache

# Time helpers
def to_minutes(t):
    # t like '9:00' or '16:30'
    h, m = t.split(":")
    return int(h) * 60 + int(m)

def fmt_time(mins):
    h = mins // 60
    m = mins % 60
    return f"{h}:{m:02d}"

# Travel times (minutes)
locations = [
    "Richmond District","The Castro","Nob Hill","Marina District","Pacific Heights",
    "Haight-Ashbury","Mission District","Chinatown","Russian Hill","Alamo Square","Bayview"
]

T = {loc: {} for loc in locations}
def set_t(a,b,v):
    T[a][b] = v

# Given pairwise travel times
set_t("Richmond District","The Castro",16)
set_t("Richmond District","Nob Hill",17)
set_t("Richmond District","Marina District",9)
set_t("Richmond District","Pacific Heights",10)
set_t("Richmond District","Haight-Ashbury",10)
set_t("Richmond District","Mission District",20)
set_t("Richmond District","Chinatown",20)
set_t("Richmond District","Russian Hill",13)
set_t("Richmond District","Alamo Square",13)
set_t("Richmond District","Bayview",27)

set_t("The Castro","Richmond District",16)
set_t("The Castro","Nob Hill",16)
set_t("The Castro","Marina District",21)
set_t("The Castro","Pacific Heights",16)
set_t("The Castro","Haight-Ashbury",6)
set_t("The Castro","Mission District",7)
set_t("The Castro","Chinatown",22)
set_t("The Castro","Russian Hill",18)
set_t("The Castro","Alamo Square",8)
set_t("The Castro","Bayview",19)

set_t("Nob Hill","Richmond District",14)
set_t("Nob Hill","The Castro",17)
set_t("Nob Hill","Marina District",11)
set_t("Nob Hill","Pacific Heights",8)
set_t("Nob Hill","Haight-Ashbury",13)
set_t("Nob Hill","Mission District",13)
set_t("Nob Hill","Chinatown",6)
set_t("Nob Hill","Russian Hill",5)
set_t("Nob Hill","Alamo Square",11)
set_t("Nob Hill","Bayview",19)

set_t("Marina District","Richmond District",11)
set_t("Marina District","The Castro",22)
set_t("Marina District","Nob Hill",12)
set_t("Marina District","Pacific Heights",7)
set_t("Marina District","Haight-Ashbury",16)
set_t("Marina District","Mission District",20)
set_t("Marina District","Chinatown",15)
set_t("Marina District","Russian Hill",8)
set_t("Marina District","Alamo Square",15)
set_t("Marina District","Bayview",27)

set_t("Pacific Heights","Richmond District",12)
set_t("Pacific Heights","The Castro",16)
set_t("Pacific Heights","Nob Hill",8)
set_t("Pacific Heights","Marina District",6)
set_t("Pacific Heights","Haight-Ashbury",11)
set_t("Pacific Heights","Mission District",15)
set_t("Pacific Heights","Chinatown",11)
set_t("Pacific Heights","Russian Hill",7)
set_t("Pacific Heights","Alamo Square",10)
set_t("Pacific Heights","Bayview",22)

set_t("Haight-Ashbury","Richmond District",10)
set_t("Haight-Ashbury","The Castro",6)
set_t("Haight-Ashbury","Nob Hill",15)
set_t("Haight-Ashbury","Marina District",17)
set_t("Haight-Ashbury","Pacific Heights",12)
set_t("Haight-Ashbury","Mission District",11)
set_t("Haight-Ashbury","Chinatown",19)
set_t("Haight-Ashbury","Russian Hill",17)
set_t("Haight-Ashbury","Alamo Square",5)
set_t("Haight-Ashbury","Bayview",18)

set_t("Mission District","Richmond District",20)
set_t("Mission District","The Castro",7)
set_t("Mission District","Nob Hill",12)
set_t("Mission District","Marina District",19)
set_t("Mission District","Pacific Heights",16)
set_t("Mission District","Haight-Ashbury",12)
set_t("Mission District","Chinatown",16)
set_t("Mission District","Russian Hill",15)
set_t("Mission District","Alamo Square",11)
set_t("Mission District","Bayview",14)

set_t("Chinatown","Richmond District",20)
set_t("Chinatown","The Castro",22)
set_t("Chinatown","Nob Hill",9)
set_t("Chinatown","Marina District",12)
set_t("Chinatown","Pacific Heights",10)
set_t("Chinatown","Haight-Ashbury",19)
set_t("Chinatown","Mission District",17)
set_t("Chinatown","Russian Hill",7)
set_t("Chinatown","Alamo Square",17)
set_t("Chinatown","Bayview",20)

set_t("Russian Hill","Richmond District",14)
set_t("Russian Hill","The Castro",21)
set_t("Russian Hill","Nob Hill",5)
set_t("Russian Hill","Marina District",7)
set_t("Russian Hill","Pacific Heights",7)
set_t("Russian Hill","Haight-Ashbury",17)
set_t("Russian Hill","Mission District",16)
set_t("Russian Hill","Chinatown",9)
set_t("Russian Hill","Alamo Square",15)
set_t("Russian Hill","Bayview",23)

set_t("Alamo Square","Richmond District",11)
set_t("Alamo Square","The Castro",8)
set_t("Alamo Square","Nob Hill",11)
set_t("Alamo Square","Marina District",15)
set_t("Alamo Square","Pacific Heights",10)
set_t("Alamo Square","Haight-Ashbury",5)
set_t("Alamo Square","Mission District",10)
set_t("Alamo Square","Chinatown",15)
set_t("Alamo Square","Russian Hill",13)
set_t("Alamo Square","Bayview",16)

set_t("Bayview","Richmond District",25)
set_t("Bayview","The Castro",19)
set_t("Bayview","Nob Hill",20)
set_t("Bayview","Marina District",27)
set_t("Bayview","Pacific Heights",23)
set_t("Bayview","Haight-Ashbury",19)
set_t("Bayview","Mission District",13)
set_t("Bayview","Chinatown",19)
set_t("Bayview","Russian Hill",23)
set_t("Bayview","Alamo Square",16)

def travel_time(a, b):
    if a == b:
        return 0
    return T[a][b]

# Constraints: people with availability windows and minimum meeting durations
start_location = "Richmond District"
arrival_time = to_minutes("9:00")

people = [
    {"name":"Matthew","location":"The Castro","start":to_minutes("16:30"),"end":to_minutes("20:00"),"min_duration":45},
    {"name":"Rebecca","location":"Nob Hill","start":to_minutes("15:15"),"end":to_minutes("19:15"),"min_duration":105},
    {"name":"Brian","location":"Marina District","start":to_minutes("14:15"),"end":to_minutes("22:00"),"min_duration":30},
    {"name":"Emily","location":"Pacific Heights","start":to_minutes("11:15"),"end":to_minutes("19:45"),"min_duration":15},
    {"name":"Karen","location":"Haight-Ashbury","start":to_minutes("11:45"),"end":to_minutes("17:30"),"min_duration":30},
    {"name":"Stephanie","location":"Mission District","start":to_minutes("13:00"),"end":to_minutes("15:45"),"min_duration":75},
    {"name":"James","location":"Chinatown","start":to_minutes("14:30"),"end":to_minutes("19:00"),"min_duration":120},
    {"name":"Steven","location":"Russian Hill","start":to_minutes("14:00"),"end":to_minutes("20:00"),"min_duration":30},
    {"name":"Elizabeth","location":"Alamo Square","start":to_minutes("13:00"),"end":to_minutes("17:15"),"min_duration":120},
    {"name":"William","location":"Bayview","start":to_minutes("18:15"),"end":to_minutes("20:15"),"min_duration":90},
]

# Index people by name
pdict = {p["name"]: p for p in people}
names = [p["name"] for p in people]

# Precompute latest feasible start times for pruning
for p in people:
    p["latest_start"] = p["end"] - p["min_duration"]

# DFS search with memoization
def pack_result(cnt, total_minutes, final_time, plan):
    return (cnt, total_minutes, -final_time, plan)  # note: earlier final_time preferred => larger -final_time

@lru_cache(maxsize=None)
def dfs(current_loc, current_time, remaining_frozen):
    remaining = list(remaining_frozen)
    # Upper bound prune: how many could possibly still be met if zero travel time
    possible_left = sum(1 for name in remaining if current_time <= pdict[name]["latest_start"])
    if possible_left == 0:
        return (0, 0, -current_time, [])  # no more meetings possible
    
    # Generate feasible next options
    candidates = []
    for name in remaining:
        p = pdict[name]
        # Travel and earliest start
        arr = current_time + travel_time(current_loc, p["location"])
        if arr > p["latest_start"]:
            continue  # cannot fit even if we start immediately upon arrival
        start = max(arr, p["start"])
        end = start + p["min_duration"]
        if end > p["end"]:
            continue
        candidates.append((name, start, end))
    
    # If no feasible next, return leaf result
    if not candidates:
        return (0, 0, -current_time, [])
    
    # Sort candidates by heuristic: earliest latest_start, then earliest end
    candidates.sort(key=lambda x: (pdict[x[0]]["latest_start"], x[2]))
    
    best = (0, 0, -current_time, [])
    # Try each candidate
    for name, start, end in candidates:
        p = pdict[name]
        new_remaining = tuple(sorted(n for n in remaining if n != name))
        sub = dfs(p["location"], end, new_remaining)
        # Build this plan
        cnt = 1 + sub[0]
        total_minutes = p["min_duration"] + sub[1]
        final_time_neg = sub[2]
        plan = [{"action":"meet","location":p["location"],"person":name,"start_time":fmt_time(start),"end_time":fmt_time(end)}] + sub[3]
        # Choose best: more people, then more total meeting time, then earlier finish (i.e., larger -final_time)
        candidate_result = (cnt, total_minutes, final_time_neg, plan)
        if candidate_result > best:
            best = candidate_result
    
    return best

# Kick off the search
remaining_all = tuple(sorted(names))
best_cnt, best_total, best_final_neg, best_plan = dfs(start_location, arrival_time, remaining_all)

# The dfs builds plan in chronological order by construction, but ensure sorted
best_plan_sorted = sorted(best_plan, key=lambda x: to_minutes(x["start_time"]))

# Output JSON
output = {"itinerary": best_plan_sorted}
print(json.dumps(output, ensure_ascii=False))