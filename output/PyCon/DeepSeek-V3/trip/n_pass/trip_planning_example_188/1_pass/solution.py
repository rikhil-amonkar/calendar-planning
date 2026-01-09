import json
from constraint import Problem

def solve_itinerary():
    # Problem parameters
    total_days = 12
    brussels_days = 2
    split_days = 5
    barcelona_days = 7
    
    # Create constraint problem
    problem = Problem()
    
    # Define variables: start days for each city stay
    # We need to determine when each city visit starts and ends
    problem.addVariable("brussels_start", range(1, total_days + 1))
    problem.addVariable("split_start", range(1, total_days + 1))
    problem.addVariable("barcelona_start", range(1, total_days + 1))
    
    # Constraint: Brussels must start on day 1 (conference requirement)
    problem.addConstraint(lambda bs: bs == 1, ["brussels_start"])
    
    # Constraint: Brussels duration is exactly 2 days
    problem.addConstraint(lambda bs: bs + brussels_days - 1 <= total_days, ["brussels_start"])
    
    # Constraint: Split duration is exactly 5 days
    problem.addConstraint(lambda ss: ss + split_days - 1 <= total_days, ["split_start"])
    
    # Constraint: Barcelona duration is exactly 7 days
    problem.addConstraint(lambda bs: bs + barcelona_days - 1 <= total_days, ["barcelona_start"])
    
    # Constraint: No overlapping stays
    def no_overlap(bs, ss, bcn):
        brussels_end = bs + brussels_days - 1
        split_end = ss + split_days - 1
        barcelona_end = bcn + barcelona_days - 1
        
        # Check if any two stays overlap
        overlaps = []
        overlaps.append(bs <= split_end and ss <= brussels_end)  # Brussels-Split overlap
        overlaps.append(bs <= barcelona_end and bcn <= brussels_end)  # Brussels-Barcelona overlap
        overlaps.append(ss <= barcelona_end and bcn <= split_end)  # Split-Barcelona overlap
        
        return not any(overlaps)
    
    problem.addConstraint(no_overlap, ["brussels_start", "split_start", "barcelona_start"])
    
    # Constraint: Total days must equal sum of individual days
    # Since we have no overlaps and fixed durations, this is automatically satisfied
    
    # Constraint: Direct flight connectivity
    # Brussels can only connect to Barcelona, Barcelona can connect to Split
    # This means the itinerary must be either:
    # 1. Brussels -> Barcelona -> Split
    # 2. Brussels -> Barcelona (and no Split if not connected)
    # But we know all three must be visited, so only option 1 is valid
    # This means Barcelona must come after Brussels and before Split, or vice versa
    
    def valid_sequence(bs, ss, bcn):
        brussels_end = bs + brussels_days - 1
        split_end = ss + split_days - 1
        barcelona_end = bcn + barcelona_days - 1
        
        # Valid sequences: Brussels -> Barcelona -> Split OR Split -> Barcelona -> Brussels
        # But Brussels must start on day 1, so only Brussels -> Barcelona -> Split is possible
        sequence1 = (brussels_end <= bcn and barcelona_end <= ss)  # Brussels -> Barcelona -> Split
        sequence2 = (split_end <= bcn and barcelona_end <= bs)     # Split -> Barcelona -> Brussels
        
        # Since Brussels starts on day 1, sequence2 is impossible
        return sequence1
    
    problem.addConstraint(valid_sequence, ["brussels_start", "split_start", "barcelona_start"])
    
    # Solve the problem
    solutions = problem.getSolutions()
    
    if not solutions:
        return {"error": "No valid itinerary found"}
    
    # Use the first valid solution
    solution = solutions[0]
    bs = solution["brussels_start"]
    ss = solution["split_start"]
    bcn = solution["barcelona_start"]
    
    brussels_end = bs + brussels_days - 1
    split_end = ss + split_days - 1
    barcelona_end = bcn + barcelona_days - 1
    
    # Create itinerary segments
    itinerary = []
    
    # Add Brussels segment
    if bs < brussels_end:
        itinerary.append({"day_range": f"Day {bs}-{brussels_end}", "place": "Brussels"})
    else:
        itinerary.append({"day_range": f"Day {bs}", "place": "Brussels"})
    
    # Add Barcelona segment
    if bcn < barcelona_end:
        itinerary.append({"day_range": f"Day {bcn}-{barcelona_end}", "place": "Barcelona"})
    else:
        itinerary.append({"day_range": f"Day {bcn}", "place": "Barcelona"})
    
    # Add Split segment
    if ss < split_end:
        itinerary.append({"day_range": f"Day {ss}-{split_end}", "place": "Split"})
    else:
        itinerary.append({"day_range": f"Day {ss}", "place": "Split"})
    
    # Sort itinerary by start day
    itinerary.sort(key=lambda x: int(x["day_range"].split(" ")[1].split("-")[0]))
    
    return {"itinerary": itinerary}

if __name__ == "__main__":
    result = solve_itinerary()
    print(json.dumps(result, indent=2))