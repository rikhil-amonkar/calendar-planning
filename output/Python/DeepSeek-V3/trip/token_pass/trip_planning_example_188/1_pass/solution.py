import json
from typing import List, Dict, Tuple

def compute_itinerary() -> Dict:
    """
    Computes the optimal itinerary for visiting Brussels, Split, and Barcelona
    over 12 days with given constraints and direct flight connections.
    """
    # Fixed constraints
    total_days = 12
    brussels_days_needed = 2
    split_days_needed = 5
    barcelona_days_needed = 7
    
    # Direct flight connections
    direct_flights = {
        ("Brussels", "Barcelona"),
        ("Barcelona", "Split")
    }
    
    # Conference constraint: Brussels on days 1 and 2
    # This means we must start in Brussels
    itinerary = []
    
    # Since we must be in Brussels on days 1-2, and we need 2 days total there,
    # we can leave Brussels after day 2.
    # From Brussels, we can only fly to Barcelona (direct connection).
    # From Barcelona, we can fly to Split.
    
    # We need to allocate:
    # Brussels: 2 days (days 1-2)
    # Split: 5 days
    # Barcelona: 7 days
    # Total: 14 days needed, but we only have 12 days.
    # This means there must be overlap on travel days.
    
    # Rule: If you fly from A to B on day X, you're in both cities on day X.
    # So travel days count toward both cities' totals.
    
    # Strategy:
    # 1. Start in Brussels (days 1-2) - conference days
    # 2. Fly to Barcelona on day 3 (counts for both Brussels and Barcelona)
    # 3. Stay in Barcelona for remaining Barcelona days
    # 4. Fly to Split on a day that counts for both Barcelona and Split
    # 5. End in Split
    
    # Let's calculate:
    # Brussels: Need 2 days total.
    # Days 1-2 in Brussels = 2 days. Requirement met.
    
    # Barcelona: Need 7 days total.
    # Day 3: Travel from Brussels to Barcelona (counts as 1 Barcelona day)
    # Need 6 more Barcelona days.
    
    # Split: Need 5 days total.
    # Last day in Barcelona will also be travel day to Split (counts as 1 Split day)
    # Need 4 more Split days.
    
    # Let's allocate:
    # Day 1-2: Brussels (2 days Brussels)
    # Day 3: Travel Brussels→Barcelona (1 day Barcelona)
    # Day 4-9: Barcelona (6 days Barcelona) → total Barcelona days = 7
    # Day 9: Travel Barcelona→Split (1 day Split, also last Barcelona day)
    # Day 10-12: Split (3 days Split) → total Split days = 4
    
    # Wait, that gives Split only 4 days, but we need 5.
    # Need to adjust to get 5 Split days.
    
    # Revised allocation:
    # Day 1-2: Brussels (2 days Brussels)
    # Day 3: Travel Brussels→Barcelona (1 day Barcelona)
    # Day 4-8: Barcelona (5 days Barcelona) → total Barcelona days = 6 so far
    # Day 9: Travel Barcelona→Split (1 day Split, 1 day Barcelona) → Barcelona total = 7, Split total = 1
    # Day 10-12: Split (3 days Split) → Split total = 4
    
    # Still only 4 Split days. Need to take one day from Barcelona.
    
    # Final working allocation:
    # Day 1-2: Brussels (2 days Brussels)
    # Day 3: Travel Brussels→Barcelona (1 day Barcelona)
    # Day 4-7: Barcelona (4 days Barcelona) → Barcelona total = 5 so far
    # Day 8: Travel Barcelona→Split (1 day Split, 1 day Barcelona) → Barcelona total = 6, Split total = 1
    # Day 9-12: Split (4 days Split) → Split total = 5
    
    # But Barcelona needs 7 days, we only have 6. Need one more Barcelona day.
    # This shows the trade-off: with 12 days total and overlap rules,
    # we can't meet all exact requirements without overlap optimization.
    
    # Let's solve systematically:
    # Let B1 = Brussels days, B2 = Barcelona days, S = Split days
    # Let T1 = day traveling Brussels→Barcelona
    # Let T2 = day traveling Barcelona→Split
    
    # Constraints:
    # 1. B1 ≥ 2 (Brussels needs at least 2 days)
    # 2. B2 ≥ 7 (Barcelona needs at least 7 days)
    # 3. S ≥ 5 (Split needs at least 5 days)
    # 4. B1 + B2 + S - overlaps = 12
    
    # Overlaps:
    # - If T1 exists, it counts for both B1 and B2
    # - If T2 exists, it counts for both B2 and S
    
    # Let x = 1 if we travel Brussels→Barcelona (always true since we must leave Brussels)
    # Let y = 1 if we travel Barcelona→Split (always true since we must reach Split)
    
    # Then: B1 + B2 + S - x - y = 12
    # B1 ≥ 2, B2 ≥ 7, S ≥ 5
    # Minimum total without overlaps: 2 + 7 + 5 = 14
    # With 2 overlaps: 14 - 2 = 12 ✓
    
    # So we need exactly:
    # B1 = 2, B2 = 7, S = 5 with both travel days overlapping.
    
    # This means:
    # Day 1-2: Brussels (2 days Brussels, no overlap yet)
    # Day 3: Travel Brussels→Barcelona (counts as Brussels day 3? No, Brussels done)
    # Actually, Brussels only needs 2 days, so day 3 is travel day that counts for Barcelona only.
    # But we need the travel day to count for both cities to reduce total.
    # So we need to travel on a day when we're still counting for the origin city.
    
    # Solution: Travel on the last day in each city.
    # Day 2: Last day in Brussels, also travel to Barcelona → counts for both Brussels and Barcelona
    # Day ?: Last day in Barcelona, also travel to Split → counts for both Barcelona and Split
    
    # Revised schedule:
    # Day 1: Brussels (1 Brussels day)
    # Day 2: Travel Brussels→Barcelona (counts as 1 Brussels day + 1 Barcelona day) → Brussels total = 2, Barcelona total = 1
    # Day 3-8: Barcelona (6 days Barcelona) → Barcelona total = 7
    # Day 8: Actually day 8 should be travel day to get overlap
    # Day 8: Travel Barcelona→Split (counts as 1 Barcelona day + 1 Split day) → Barcelona total stays at 7, Split total = 1
    # Day 9-12: Split (4 days Split) → Split total = 5
    
    # Perfect! This satisfies all constraints.
    
    # Build itinerary
    itinerary = []
    
    # Day 1: Brussels only
    itinerary.append({"day_range": "Day 1", "place": "Brussels"})
    
    # Day 2: Travel Brussels→Barcelona (counts for both)
    itinerary.append({"day_range": "Day 2", "place": "Brussels → Barcelona"})
    
    # Day 3-7: Barcelona only (5 days)
    itinerary.append({"day_range": "Day 3-7", "place": "Barcelona"})
    
    # Day 8: Travel Barcelona→Split (counts for both)
    itinerary.append({"day_range": "Day 8", "place": "Barcelona → Split"})
    
    # Day 9-12: Split only (4 days)
    itinerary.append({"day_range": "Day 9-12", "place": "Split"})
    
    # Verify totals
    brussels_count = 0
    barcelona_count = 0
    split_count = 0
    
    for entry in itinerary:
        place = entry["place"]
        day_range = entry["day_range"]
        
        # Parse day range to count days
        if "-" in day_range:
            days = day_range.replace("Day ", "").split("-")
            start = int(days[0])
            end = int(days[1])
            num_days = end - start + 1
        else:
            num_days = 1
        
        # Count based on place
        if place == "Brussels":
            brussels_count += num_days
        elif place == "Barcelona":
            barcelona_count += num_days
        elif place == "Split":
            split_count += num_days
        elif "Brussels → Barcelona" in place:
            brussels_count += 1
            barcelona_count += 1
        elif "Barcelona → Split" in place:
            barcelona_count += 1
            split_count += 1
    
    # Check constraints
    assert brussels_count == 2, f"Brussels days: {brussels_count}, expected 2"
    assert barcelona_count == 7, f"Barcelona days: {barcelona_count}, expected 7"
    assert split_count == 5, f"Split days: {split_count}, expected 5"
    assert brussels_count + barcelona_count + split_count - 2 == 12, "Total days incorrect"
    
    return {"itinerary": itinerary}

def main():
    """Main function to compute and output itinerary as JSON."""
    result = compute_itinerary()
    print(json.dumps(result, indent=2))

if __name__ == "__main__":
    main()