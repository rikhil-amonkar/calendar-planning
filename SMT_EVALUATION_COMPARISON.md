# SMT Evaluation Methods Comparison

## Files Analyzed

1. **`iterative_smt_refinement_enhanced.py`** - Enhanced version with improved evaluation
2. **`iterative_smt_refinement.py`** - Original version
3. **`iterative_smt_refinement_parallel.py`** - Parallel version (no evaluation functions)

## Key Findings

### **Calendar Evaluation (`evaluate_calendar`)**

#### **iterative_smt_refinement_enhanced.py**
```python
def evaluate_calendar(constraints, pred_dict):
    # Check for no_plan cases first
    if isinstance(pred_dict, dict) and ("no_plan" in pred_dict or "error" in pred_dict):
        return False, {"no_plan": pred_dict.get("no_plan", pred_dict.get("error", "unknown"))}
    
    # Check for missing day, start_time, or end_time
    if not pred_dict or "day" not in pred_dict or "start_time" not in pred_dict or "end_time" not in pred_dict:
        return False, {"missing_fields": True}
    
    # ... rest of validation logic
    meeting_duration = constraints.get("meeting_duration")
    if meeting_duration is None:
        return False, {"missing_meeting_duration": True}
```

#### **iterative_smt_refinement.py**
```python
def evaluate_calendar(constraints, pred_dict):
    """Evaluate calendar constraints"""
    if not pred_dict or "day" not in pred_dict or "start_time" not in pred_dict or "end_time" not in pred_dict:
        return False, {"missing_fields": True}
    
    # ... rest of validation logic
    meeting_duration = constraints["meeting_duration"]  # Direct access, no .get()
```

#### **Key Differences:**

1. **✅ Enhanced: No-plan handling**
   - Enhanced version checks for `no_plan` or `error` cases first
   - Original version doesn't handle these cases

2. **✅ Enhanced: Robust meeting_duration access**
   - Enhanced: `constraints.get("meeting_duration")` with None check
   - Original: `constraints["meeting_duration"]` (direct access, may fail)

3. **✅ Enhanced: Better error handling**
   - Enhanced version provides more specific error messages
   - Original version has basic error handling

---

### **Trip Evaluation (`evaluate_trip`)**

#### **iterative_smt_refinement_enhanced.py**
```python
def evaluate_trip(constraints, pred_dict):
    # Check for no_plan cases first
    if isinstance(pred_dict, dict) and ("no_plan" in pred_dict or "error" in pred_dict):
        return False, {"no_plan": pred_dict.get("no_plan", pred_dict.get("error", "unknown"))}
    
    # parse the predicted itinerary segments
    segments = []
    for seg in pred_dict["itinerary"]:
        # Handle special cases like "Day {current_day}-{current_day + 2}"
        if not seg["day_range"].startswith("Day ") or "{" in seg["day_range"] or "}" in seg["day_range"]:
            return False, {"invalid_day_range_format": seg["day_range"]}
        # ... rest of parsing
    
    # Sort segments by start day to ensure chronological order for constraint evaluation
    segments.sort(key=lambda x: x["start"])
    
    # 1) check full coverage from day 1 to total_days, with no gaps/overlaps
    total = constraints.get("trip_length")
    if not segments or segments[0]["start"] != 1 or segments[-1]["end"] != total:
        return False, {"total_days": total}
    for a, b in zip(segments, segments[1:]):
        if a["end"] != b["start"]:
            return False, {"gap/overlap": (a, b)}
    
    # 2) check each place's stay duration
    # Handle both 'stay_days' (dict) and 'city_length' (array) formats
    stay_days_dict = {}
    if "stay_days" in constraints:
        stay_days_dict = constraints["stay_days"]
    elif "city_length" in constraints:
        for city_info in constraints["city_length"]:
            stay_days_dict[city_info["city"]] = city_info["days"]
    
    # 3) check event_ranges (must fall entirely within the visit segment)
    for ev in constraints.get("city_day_ranges", []):
        place = ev["city"]
        container = next((s for s in segments if s["place"] == place), None)
        if not container:
            return False, {"missing_place": place}
```

#### **iterative_smt_refinement.py**
```python
def evaluate_trip(constraints, pred_dict):
    """Evaluate trip constraints"""
    segments = []
    for seg in pred_dict["itinerary"]:
        if not seg["day_range"].startswith("Day ") or "{" in seg["day_range"] or "}" in seg["day_range"]:
            return False, {"invalid_day_range_format": seg["day_range"]}
        # ... rest of parsing
    
    total = constraints.get("trip_length")
    if not segments or segments[0]["start"] != 1 or segments[-1]["end"] != total:
        return False, {"total_days": total}

    for a, b in zip(segments, segments[1:]):
        # Only check gap/overlap for different places
        # For the same place, we allow overlaps and gaps (flight days, duplicates, etc.)
        if a["place"] != b["place"] and a["end"] != b["start"]:
            return False, {"gap/overlap": (a, b)}

    for seg in segments:
        required = constraints.get("stay_days", {}).get(seg["place"])
        if required is not None:
            actual = seg["end"] - seg["start"] + 1
            if actual != required:
                return False, {"stay_days": {seg["place"]: required}}

    # Fix: Check event ranges against ALL segments for a place, not just the first one
    for ev in constraints.get("city_day_ranges", []):
        place = ev["city"]
        place_segments = [s for s in segments if s["place"] == place]
        if not place_segments:
            return False, {"missing_place": place}
        
        # Check if the event range is covered by any combination of segments for this place
        event_covered = False
        for seg in place_segments:
            if seg["start"] <= ev["start"] and seg["end"] >= ev["end"]:
                event_covered = True
                break
        
        if not event_covered:
            return False, {"event_range": ev}
```

#### **Key Differences:**

1. **✅ Enhanced: No-plan handling**
   - Enhanced version checks for `no_plan` or `error` cases first
   - Original version doesn't handle these cases

2. **✅ Enhanced: Chronological sorting**
   - Enhanced: `segments.sort(key=lambda x: x["start"])` for proper constraint evaluation
   - Original: No explicit sorting

3. **❌ Enhanced: Stricter gap/overlap checking**
   - Enhanced: Checks ALL consecutive segments for gaps/overlaps
   - Original: Only checks different places (allows overlaps for same place)

4. **✅ Enhanced: Flexible stay_days handling**
   - Enhanced: Handles both `stay_days` (dict) and `city_length` (array) formats
   - Original: Only handles `stay_days` format

5. **❌ Enhanced: Simpler event range checking**
   - Enhanced: Uses `next()` to find first matching segment
   - Original: Checks ALL segments for a place (more comprehensive)

---

### **Meeting Evaluation (`evaluate_meeting`)**

#### **iterative_smt_refinement_enhanced.py**
```python
def evaluate_meeting(constraints, pred_dict):
    # Check for no_plan cases first
    if isinstance(pred_dict, dict) and ("no_plan" in pred_dict or "error" in pred_dict):
        return False, {"no_plan": pred_dict.get("no_plan", pred_dict.get("error", "unknown"))}

    # build map person→availability & location
    people = {p["name"]: p for p in constraints.get("people_to_meet", [])}
    start_location = constraints.get("start", {}).get("location")
    start_time = constraints.get("start", {}).get("time_of_day")
    num_people_to_meet = constraints.get("num_people_to_meet", 0)

    # parse predicted meetings
    meetings = []
    for m in pred_dict.get("itinerary", []):
        name = m["person"]
        start = parse_time(m["start_time"])
        end = parse_time(m["end_time"])
        if start is None or end is None:  # Invalid time format
            return False, {"invalid_time_format": {"start": m["start_time"], "end": m["end_time"]}}
        loc = people.get(name, {}).get("location")
        meetings.append({"person": name, "start": start, "end": end, "location": loc})

    if len(meetings) < num_people_to_meet:
        return False, {"num_people_to_meet": num_people_to_meet}
    # sort chronologically
    meetings.sort(key=lambda x: x["start"])

    # 1) each meeting must lie within that person's available window
    for m in meetings:
        p = people.get(m["person"])
        if not p:
            continue
        avail = p["time_of_day"]
        av_from = parse_time(avail["from"])
        av_to = parse_time(avail["to"])
        if m["start"] < av_from or m["end"] > av_to:
            return False, {"person": m["person"], "time_of_day": avail}

    # 2) build travel‐time lookup
    travel = {}
    for d in constraints.get("travel_distances", []):
        pl = d["place"]
        frm = pl.get("from", constraints.get("start", {}).get("location"))
        to = pl["to"]
        travel[(frm, to)] = d["walking_time"]

    # 3) check start‐to‐first meeting
    # parse start time
    if start_time and meetings:
        st = parse_time(start_time)
        first = meetings[0]
        # 0a) meeting must not start before you arrive
        if first["start"] < st:
            return False, {"start_time": start_time}
        # 0b) travel from start_location
        walk0 = travel.get((start_location, first["location"]))
        gap0 = (first["start"] - st).total_seconds() / 60
        if walk0 is not None and walk0 > gap0:
            return False, {
                "travel_start": {
                    "to_person": first["person"],
                    "to_location": first["location"],
                    "travel_time": walk0
                }
            }

    # 3) check following meetings
    for a, b in zip(meetings, meetings[1:]):
        gap_mins = (b["start"] - a["end"]).total_seconds() / 60
        walk = travel.get((a["location"], b["location"]))
        if walk is not None and walk > gap_mins:
            return False, {
                "travel": {
                    "from_person": a["person"],
                    "to_person": b["person"],
                    "from_location": a["location"],
                    "to_location": b["location"],
                    "travel_time": walk
                }
            }

    return True, {}
```

#### **iterative_smt_refinement.py**
```python
def evaluate_meeting(constraints, pred_dict):
    """Evaluate meeting constraints"""
    # Handle nested constraints structure
    actual_constraints = constraints.get("constraints", constraints)
    
    def parse_time(s):
        try:
            if s.endswith(("AM", "PM")):
                return datetime.strptime(s, "%I:%M%p")
            return datetime.strptime(s, "%H:%M")
        except ValueError:
            return None

    people = {p["name"]: p for p in constraints.get("people_to_meet", [])}
    start_location = constraints.get("start", {}).get("location")
    start_time = constraints.get("start", {}).get("time_of_day")
    num_people_to_meet = constraints.get("num_people_to_meet", 0)

    meetings = []
    for m in pred_dict.get("itinerary", []):
        name = m["person"]
        start = parse_time(m["start_time"])
        end = parse_time(m["end_time"])
        if start is None or end is None:
            return False, {"invalid_time_format": {"start": m["start_time"], "end": m["end_time"]}}
        loc = people.get(name, {}).get("location")
        meetings.append({"person": name, "start": start, "end": end, "location": loc})

    if len(meetings) < num_people_to_meet:
        return False, {"num_people_to_meet": num_people_to_meet}

    if not meetings:
        return True, {}

    meetings.sort(key=lambda x: x["start"])

    for m in meetings:
        p = people.get(m["person"])
        if not p:
            continue
        avail = p["time_of_day"]
        av_from = parse_time(avail["from"])
        av_to = parse_time(avail["to"])
        if m["start"] < av_from or m["end"] > av_to:
            return False, {"person": m["person"], "time_of_day": avail}

    travel = {}
    for d in actual_constraints.get("travel_distances", []):
        pl = d["place"]
        frm = pl.get("from", actual_constraints.get("start", {}).get("location"))
        to = pl["to"]
        travel[(frm, to)] = d["walking_time"]

    if start_time:
        st = parse_time(start_time)
        first = meetings[0]
        if first["start"] < st:
            return False, {"start_time": start_time}
        walk0 = travel.get((start_location, first["location"]))
        gap0 = (first["start"] - st).total_seconds() / 60
        if walk0 is not None and walk0 > gap0:
            return False, {
                "travel_start": {
                    "to_person": first["person"],
                    "to_location": first["location"],
                    "travel_time": walk0
                }
            }

    for a, b in zip(meetings, meetings[1:]):
        gap_mins = (b["start"] - a["end"]).total_seconds() / 60
        walk = travel.get((a["location"], b["location"]))
        if walk is not None and walk > gap_mins:
            return False, {
                "travel": {
                    "from_person": a["person"],
                    "to_person": b["person"],
                    "from_location": a["location"],
                    "to_location": b["location"],
                    "travel_time": walk
                }
            }

    return True, {}
```

#### **Key Differences:**

1. **✅ Enhanced: No-plan handling**
   - Enhanced version checks for `no_plan` or `error` cases first
   - Original version doesn't handle these cases

2. **❌ Original: Nested constraints handling**
   - Original: `actual_constraints = constraints.get("constraints", constraints)`
   - Enhanced: Direct access to constraints

3. **❌ Original: Empty meetings handling**
   - Original: `if not meetings: return True, {}`
   - Enhanced: No special handling for empty meetings

4. **✅ Enhanced: Better error handling**
   - Enhanced version provides more specific error messages
   - Original version has basic error handling

---

## Summary of Differences

### **Enhanced Version Improvements:**

1. **✅ No-plan/Error Handling**: All evaluation functions check for `no_plan` or `error` cases first
2. **✅ Robust Constraint Access**: Uses `.get()` with default values instead of direct access
3. **✅ Better Error Messages**: More specific error information
4. **✅ Chronological Sorting**: Trip evaluation sorts segments for proper constraint evaluation
5. **✅ Flexible Format Support**: Trip evaluation handles both `stay_days` and `city_length` formats

### **Original Version Features:**

1. **❌ Original: Nested Constraints**: Meeting evaluation handles nested constraint structures
2. **❌ Original: Empty Meeting Handling**: Calendar evaluation has special handling for empty meetings
3. **❌ Original: Comprehensive Event Range Checking**: Trip evaluation checks ALL segments for event coverage
4. **❌ Original: Flexible Gap/Overlap**: Trip evaluation allows overlaps for same place

### **Missing in Parallel Version:**

The `iterative_smt_refinement_parallel.py` file **does not contain any evaluation functions**. It appears to be focused on parallel processing infrastructure rather than evaluation logic.

## Recommendation

The **enhanced version** (`iterative_smt_refinement_enhanced.py`) provides the most robust evaluation with:
- Better error handling
- No-plan case handling
- Robust constraint access
- Comprehensive validation

However, the **original version** has some unique features that might be worth preserving:
- Nested constraints handling for meetings
- More flexible gap/overlap checking for trips
- Comprehensive event range validation 