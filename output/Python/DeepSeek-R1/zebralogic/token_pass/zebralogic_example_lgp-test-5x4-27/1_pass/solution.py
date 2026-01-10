import json

def main():
    # Initialize the attributes for 5 houses (index 0 to 4 represent house 1 to 5)
    names = [None] * 5
    birthdays = [None] * 5
    cigars = [None] * 5
    drinks = [None] * 5

    # Apply clue 13: Eric is in the third house.
    names[2] = 'Eric'

    # Apply clue 1: The root beer lover is Eric.
    drinks[2] = 'root beer'

    # Apply clue 2: Pall Mall smoker in third house.
    cigars[2] = 'pall mall'

    # Apply clue 8: February birthday in second house.
    birthdays[1] = 'feb'

    # Apply clue 7: Blends smoker has February birthday.
    cigars[1] = 'blends'

    # Apply clue 3: Bob has April birthday.
    # (We don't know the house yet)

    # Apply clue 5: Peter is right of root beer lover (house 3)
    # So Peter in house 4 or 5 (index 3 or 4)

    # Apply clue 9: Arnold directly left of Peter.
    # Possible pairs: (0,1), (1,2), (2,3), (3,4)
    # But house 2 is Eric, so Arnold cannot be in house 2.
    # Also, Peter must be in 4 or 5, so only possible: Arnold in 3 and Peter in 4, or Arnold in 4 and Peter in 5.
    # But house 3 is Eric, so Arnold cannot be in 3. Therefore: Arnold in 4, Peter in 5.
    names[3] = 'Arnold'
    names[4] = 'Peter'

    # The only name left for house 1 is Alice.
    names[0] = 'Alice'
    # But wait, we have Bob to place. Actually, we have names: Peter, Alice, Eric, Bob, Arnold.
    # We have assigned Eric (2), Arnold (3), Peter (4), Alice (0). So Bob must be in house 1? But house 1 is index0, which we set to Alice.
    # Correction: We have five houses: index0=house1, index1=house2, index2=house3, index3=house4, index4=house5.
    # We set house3 (index2) to Eric, house4 (index3) to Arnold, house5 (index4) to Peter, and then we set house1 (index0) to Alice.
    # Then house2 (index1) must be Bob? But we have clue 3: Bob has April birthday. We haven't placed Bob yet.
    # Actually, we have not assigned house2's name. So we must assign Bob to house2?
    # But wait, we have assigned all names: 
    #   house1: Alice (index0)
    #   house2: ? -> must be Bob
    #   house3: Eric
    #   house4: Arnold
    #   house5: Peter
    # So house2 (index1) must be Bob.
    names[1] = 'Bob'

    # Apply clue 6: One house between January birthday and Peter.
    # Peter is in house5 (index4). So the January birthday must be in house3 (index2) because |3-5|=2 (with house4 between).
    birthdays[2] = 'jan'

    # Now, we have birthdays: house2 (index1) has feb, house3 (index2) has jan.
    # Bob (house2) has april birthday (clue3), but wait: we assigned house2 to Bob, and clue3 says Bob has april birthday, but we already set house2 birthday to feb? Contradiction?
    # Correction: We set birthdays[1] (house2) to feb from clue8. But clue3 says Bob has april birthday. So Bob cannot be in house2.
    # Therefore, our name assignment must be wrong.

    # Let's reexamine the name assignment:
    # We have five names: Peter, Alice, Eric, Bob, Arnold.
    # We know: 
    #   house3: Eric
    #   house4: Arnold (from clue9 and clue5)
    #   house5: Peter (from clue5 and clue9)
    # So the remaining names: Alice and Bob for house1 and house2.
    # But clue3: Bob has april birthday.
    # Clue8: house2 has feb birthday.
    # So Bob cannot be in house2 (because feb != april). Therefore, Bob must be in house1, and Alice in house2.
    names[0] = 'Bob'
    names[1] = 'Alice'

    # Now, clue3: Bob has april birthday -> so house1 birthday = april.
    birthdays[0] = 'april'

    # We already have house2 birthday = feb (clue8), and house3 birthday = jan (from clue6).
    # The remaining birthdays: mar and sept for house4 and house5.

    # Apply clue4: Dunhill smoker has march birthday.
    # So the house with march birthday will have cigar dunhill.

    # Now, cigars: we have house2: blends (from clue7 and clue8), house3: pall mall.
    # Remaining cigars: dunhill, prince, blue master.

    # Drinks: we have house3: root beer.
    # Clue10: milk not in house5 -> so milk in house1,2,3,4 but house3 has root beer, so milk in house1,2, or4.
    # Clue11: blue master smoker is coffee drinker.
    # Clue12: one house between tea and coffee.

    # Determine coffee position:
    # If coffee in house0 (house1): then tea must be in house2 (because |0-2|=2) -> but then house2 would have tea, and coffee in house0.
    # If coffee in house1 (house2): then tea must be in house3 (|1-3|=2) -> but house3 has root beer, not tea -> invalid.
    # If coffee in house2 (house3): but house3 has root beer -> invalid.
    # If coffee in house3 (house4): then tea must be in house1 (|3-1|=2) or house5 (|3-5|=2) -> so tea in house1 or house5.
    # If coffee in house4 (house5): then tea must be in house2 (|4-2|=2) -> but house2 could have tea.

    # But note: clue11: blue master smoker is coffee drinker. So the coffee drinker must also smoke blue master.
    # Now, house2 smokes blends, so if coffee is in house2, it would require blue master, but it has blends -> invalid. So coffee cannot be in house2.
    # Similarly, house3 has pall mall and root beer -> not coffee.
    # So coffee can be in house0, house3, or house4.

    # But from above:
    #   coffee in house0: then tea in house2 -> valid.
    #   coffee in house3: then tea in house1 or house5 -> valid.
    #   coffee in house4: then tea in house2 -> valid.

    # However, we also have the blue master cigar must be with coffee.
    # The blue master cigar is not in house2 (blends) or house3 (pall mall), so it must be in house0, house1, house4, or house5.
    # But house1 is Alice, and we don't know her cigar yet.

    # Now, let's consider the coffee possibilities:

    # Option 1: coffee in house0 (house1)
    #   Then blue master must be in house0 -> so house0 cigar=blue master.
    #   Then tea must be in house2 (from clue12). So house2 drink=tea.
    #   Then remaining drinks: milk and water for house3 and house4 and house5, but house3 has root beer, so milk and water for house4 and house5.
    #   But clue10: milk not in house5 -> so milk in house4, and water in house5.
    #   Now, cigars: house0: blue master, house1: ?, house2: blends, house3: pall mall, house4: ?, house5: ?
    #   The remaining cigars: dunhill and prince.
    #   The remaining houses for cigars: house1, house4, house5.
    #   But we have clue4: dunhill smoker has march birthday.
    #   The march birthday is in house4 or house5 (since house0:april, house1:feb, house2:jan? wait no: house0:april, house1:feb, house2:jan, so house3 and house4 have mar and sept).
    #   Actually, we have birthdays: house0:april, house1:feb, house2:jan, so house3 and house4 have mar and sept? But wait, we have house3 and house4 and house5? We have 5 houses.
    #   Actually, houses: 0,1,2,3,4 -> representing house1,2,3,4,5.
    #   So birthdays left: mar and sept for house3 and house4 and house5? But we have only two left, so actually house3, house4, and house5: but we already assigned house3 birthday? Wait, we assigned house2 (index2) to jan? Actually, we set birthdays[2] = jan for house3.
    #   So the remaining birthdays are mar and sept for house4 and house5.
    #   So the march birthday is in house4 or house5.
    #   Therefore, dunhill must be in the house with march birthday, i.e., house4 or house5.
    #   Now, if coffee is in house0, then we have assigned house0 cigar=blue master, so dunhill cannot be in house0.
    #   So dunhill in house4 or house5.
    #   Then prince must be in the remaining house (house1) among house1,4,5.
    #   But house1 is index1 (house2), which already has cigar blends? Wait, no: house1 is index1, which we have assigned cigar blends? Actually, we assigned cigars[1] = blends for house2.
    #   So the cigars for house1 (index0) is blue master (in this option), and house2 (index1) is blends, house3 (index2) is pall mall.
    #   So the remaining houses for cigars are house4 and house5 (index3 and index4).
    #   So prince and dunhill for house4 and house5.
    #   This seems possible.

    # Option 2: coffee in house3 (house4)
    #   Then blue master must be in house3 -> cigar[3]=blue master.
    #   Then tea must be in house1 or house5 (because |3-1|=2 and |3-5|=2).
    #   Now, if tea in house1, then house1 drink=tea.
    #   Then remaining drinks: milk and water for house0 and house5 (since house2 drink is not assigned yet? and house3 has root beer, house4 has coffee).
    #   But clue10: milk not in house5 -> so milk must be in house0, and water in house5.
    #   Then house2 drink must be the only one left? But we have five drinks: water, coffee, tea, milk, root beer.
    #   Actually, we have: house0: milk, house1: tea, house2: ?, house3: root beer, house4: coffee, house5: water.
    #   So house2 must be the remaining drink? But we have assigned all drinks? Wait, we have five drinks: we have assigned house0,1,3,4,5. So house2 must be the one missing? But we have not assigned house2 drink. But we have used all drinks: water, coffee, tea, milk, root beer. So house2 must be one of them, but which? We have not assigned it. This is inconsistent because we have five houses and five drinks.
    #   Actually, we have house2 drink unassigned, and the drinks left: none? Because we assigned house0,1,3,4,5. So we missed house2. This means we must assign house2 drink to one of the drinks, but we have already assigned all drinks to other houses. So Option2 with tea in house1 is invalid because it would require assigning house0,1,3,4,5 and leave house2 unassigned.

    #   Alternatively, if tea in house5, then house5 drink=tea.
    #   Then remaining drinks: milk and water for house0 and house2.
    #   But clue10: milk not in house5 -> already satisfied.
    #   So house0 and house2: milk and water.
    #   Now, we have house4: coffee and blue master.
    #   Cigars: we have house2: blends, house3: pall mall, house4: blue master.
    #   Remaining cigars: dunhill and prince for house0 and house5.
    #   And birthdays: house4 and house5 have mar and sept.
    #   clue4: dunhill smoker has march birthday -> so if house4 has march birthday, then it should have dunhill, but it has blue master -> contradiction.
    #   Therefore, house4 cannot have march birthday, so house4 has sept birthday, and house5 has march birthday.
    #   Then house5 must have dunhill cigar.
    #   Then house0 must have prince cigar.
    #   Now, drinks: house0 and house2: milk and water.
    #   But clue10: milk not in house5 -> already satisfied, and milk must be in house0 or house2.
    #   This is possible.

    # Option 3: coffee in house4 (house5)
    #   Then blue master in house4 -> cigar[4]=blue master.
    #   Then tea must be in house2 (|4-2|=2).
    #   So house2 drink=tea.
    #   Then remaining drinks: milk and water for house0 and house3, but house3 has root beer -> already assigned. So actually, we have house0, house1, and house3? Wait, we have house0, house1, house2, house3, house4.
    #   We have assigned: house2: tea, house3: root beer, house4: coffee.
    #   So left: milk and water for house0 and house1.
    #   But clue10: milk not in house5 -> house4 is house5? wait, index4 is house5. So milk cannot be in house4 (which is house5) -> already satisfied. So milk can be in house0 or house1.
    #   Now, cigars: house2: blends, house3: pall mall, house4: blue master.
    #   Remaining cigars: dunhill and prince for house0 and house1.
    #   Birthdays: house4 and house5 have mar and sept? wait, house4 is index4 (house5) and house5 doesn't exist? We have only indices0-4.
    #   Actually, the march birthday must be in house4 or house5? But house5 is index4. So march birthday is in house4 (index4) or house3 (index3) or house2 (index2) but house2 has jan, house1 has feb, house0 has april. So march must be in house3 or house4.
    #   clue4: dunhill smoker has march birthday.
    #   If march is in house3, then house3 must have dunhill, but house3 has pall mall -> invalid.
    #   If march is in house4, then house4 must have dunhill, but house4 has blue master -> invalid.
    #   Therefore, Option3 is invalid.

    # So only Option1 and Option2 are possible, but Option2 with tea in house5 led to a valid state.

    # Let's recheck Option1: coffee in house0 (house1)
    #   Then house0 drink=coffee, and house0 cigar=blue master (because blue master is coffee drinker).
    #   Then tea must be in house2: so house2 drink=tea.
    #   Then drinks left: milk and water for house3 and house4 and house5? But house3 has root beer, so for house4 and house5: milk and water.
    #   But clue10: milk not in house5 -> so milk in house4, water in house5.
    #   Cigars: house0: blue master, house1: blends, house2: ?, house3: pall mall, house4: ?, house5: ?
    #   Actually, we have not assigned house2 cigar? But we did: house1 (index1) is blends for house2. So house2 has cigar blends.
    #   So the remaining cigars: dunhill and prince for house3 and house4 and house5? But house3 has pall mall, so for house4 and house5: dunhill and prince.
    #   Birthdays: house0: april, house1: feb, house2: jan, so house3 and house4 have mar and sept.
    #   clue4: dunhill smoker has march birthday -> so the house with march birthday must have dunhill.
    #   March birthday is in house3 or house4.
    #   If march in house3, then house3 must have dunhill, but house3 has pall mall -> invalid.
    #   If march in house4, then house4 must have dunhill.
    #   Then house5 must have prince.
    #   So house4: birthday=mar, cigar=dunhill, drink=milk.
    #   house5: birthday=sept, cigar=prince, drink=water.
    #   But wait, house4 is index3 (house4) and house5 is index4 (house5).
    #   This seems valid.

    # Now, Option2 with tea in house5: 
    #   coffee in house3 (house4) -> drink[3]=coffee, cigar[3]=blue master.
    #   tea in house5 -> drink[4]=tea.
    #   Then drinks left: milk and water for house0 and house1.
    #   clue10: milk not in house5 -> satisfied.
    #   So house0 and house1: milk and water.
    #   Cigars: house1: blends, house2: pall mall, house3: blue master.
    #   Remaining cigars: dunhill and prince for house0 and house4.
    #   Birthdays: house0: april, house1: feb, house2: jan, so house3 and house4 have mar and sept.
    #   clue4: dunhill smoker has march birthday.
    #   If march in house3, then house3 must have dunhill, but house3 has blue master -> invalid.
    #   If march in house4, then house4 must have dunhill.
    #   Then house0 must have prince.
    #   So house4: birthday=mar, cigar=dunhill, drink=tea.
    #   But house4 is index3? wait, no: house4 is index3? Actually, we have:
    #       house3: index2 -> Eric, root beer, pall mall, jan
    #       house4: index3 -> Arnold, coffee, blue master, ? birthday
    #       house5: index4 -> Peter, tea, ?, ? birthday
    #   In this option, we have coffee in house4 (index3) and tea in house5 (index4).
    #   So for house4 (index3): drink=coffee, cigar=blue master, and birthday must be sept (because march is in house5).
    #   Then house5: birthday=mar, cigar=dunhill, drink=tea.
    #   Then house0 and house1: milk and water.
    #   This is also valid.

    # But wait, we have two options? We need to use another constraint.

    # Let's list the two options:

    # Option1:
    #   house0: name=Bob, birthday=april, cigar=blue master, drink=coffee
    #   house1: name=Alice, birthday=feb, cigar=blends, drink=tea
    #   house2: name=Eric, birthday=jan, cigar=pall mall, drink=root beer
    #   house3: name=Arnold, birthday=mar, cigar=dunhill, drink=milk
    #   house4: name=Peter, birthday=sept, cigar=prince, drink=water

    # Option2:
    #   house0: name=Bob, birthday=april, cigar=prince, drink=[milk or water]
    #   house1: name=Alice, birthday=feb, cigar=blends, drink=[water or milk]
    #   house2: name=Eric, birthday=jan, cigar=pall mall, drink=root beer
    #   house3: name=Arnold, birthday=sept, cigar=blue master, drink=coffee
    #   house4: name=Peter, birthday=mar, cigar=dunhill, drink=tea

    # We have clue10: milk not in house5. In Option1, milk is in house4 (which is house5) -> violates clue10.
    # In Option1, house3 is house4? wait, index3 is house4, and index4 is house5.
    # In Option1, house3 (index3) has drink=milk, and house3 is house4? No: index3 represents house4.
    # But clue10 says milk not in house5. In Option1, milk is in house4 (index3), which is not house5. So it is allowed.
    # However, in Option1, house5 (index4) has drink=water, which is fine.

    # But in Option2, house5 (index4) has drink=tea, which is also fine.

    # Now, let's check clue5: Peter is right of root beer lover. Root beer lover is in house3 (index2). Peter is in house5 (index4) in both options -> satisfied.

    # clue6: one house between jan birthday and Peter. Jan birthday is in house3 (index2), Peter in house5 (index4) -> between them is house4 (index3) -> satisfied.

    # clue4: Dunhill smoker is march birthday. In Option1, Dunhill is in house3 (index3) and march birthday is in house3 -> satisfied.
    # In Option2, Dunhill is in house4 (index4) and march birthday is in house4 -> satisfied.

    # clue7: Blends smoker is feb birthday. In both options, Blends is in house1 (index1) and feb birthday is in house1 -> satisfied.

    # clue8: feb birthday in second house -> house1 (index1) is second house -> satisfied.

    # clue9: Arnold left of Peter. In both options, Arnold is in house3 (index3) and Peter in house4 (index4) in Option1? wait, in Option1, Arnold is in house3 (index3) and Peter in house4 (index4) -> but house3 is left of house4 -> satisfied.
    # In Option2, Arnold is in house3 (index3) and Peter in house4 (index4) -> satisfied.

    # clue10: milk not in house5. In Option1, milk is in house3 (index3) which is house4 -> satisfied.
    # In Option2, milk is in either house0 or house1 -> satisfied.

    # clue11: blue master is coffee drinker. In Option1, blue master is in house0 (index0) and coffee in house0 -> satisfied.
    # In Option2, blue master is in house3 (index3) and coffee in house3 -> satisfied.

    # clue12: one house between tea and coffee.
    #   In Option1: coffee in house0 (index0), tea in house1 (index1) -> |0-1|=1 -> not one house between. They are adjacent.
    #   But clue12 says "one house between", which means they are two apart. For example, between house1 and house3 there is house2.
    #   So |0-1| does not have one house between. Therefore, Option1 is invalid.

    # Therefore, only Option2 is valid.

    # So we proceed with Option2.

    # Option2:
    #   house0: name=Bob, birthday=april, cigar=prince, drink=?
    #   house1: name=Alice, birthday=feb, cigar=blends, drink=?
    #   house2: name=Eric, birthday=jan, cigar=pall mall, drink=root beer
    #   house3: name=Arnold, birthday=sept, cigar=blue master, drink=coffee
    #   house4: name=Peter, birthday=mar, cigar=dunhill, drink=tea

    # Now, drinks for house0 and house1: milk and water.
    # clue10: milk not in house5 -> already satisfied.
    # We need to assign milk and water to house0 and house1.

    # Is there any constraint that can determine which?
    # We have no other clue that involves milk or water specifically.

    # But wait, we have clue4 already used.

    # So either assignment is possible? But let's see if there is any constraint.

    # We have not used clue10 anymore.

    # Actually, we have no other constraint. So both assignments are valid? But then the solution would not be unique.

    # Let's check the original clues again.

    # Clue10: "The person who likes milk is not in the fifth house." -> already satisfied.

    # So indeed, we have two possibilities for house0 and house1 drinks.

    # But wait, in Option2, we have house4 drink=tea. And house0 and house1: milk and water.

    # However, we might have missed something.

    # Let's list the drinks in Option2:
    #   house0: either milk or water
    #   house1: the other
    #   house2: root beer
    #   house3: coffee
    #   house4: tea

    # This seems to satisfy all clues.

    # But is there any clue that might relate to milk or water? We have no clue that says anything else about milk or water.

    # Therefore, the solution is not unique? But that can't be because the puzzle should have a unique solution.

    # Let's double-check clue6: "There is one house between the person whose birthday is in January and Peter."
    # In Option2, January birthday is in house2, Peter in house4 -> between them is house3 -> one house between -> satisfied.

    # clue5: Peter is right of root beer lover: root beer in house2, Peter in house4 -> right -> satisfied.

    # clue12: one house between tea and coffee. In Option2, tea is in house4, coffee in house3 -> |3-4|=1 -> adjacent, not one house between.
    # This is the problem: |3-4| does not have one house between. They are adjacent.

    # Therefore, Option2 is invalid because clue12 requires one house between, so the positions must be two apart.

    # So Option2 is invalid.

    # Therefore, the only remaining option is Option1 with coffee in house0 and tea in house2, but we already saw that Option1 has house0 and house1 adjacent for coffee and tea, which doesn't satisfy clue12.

    # Wait, we must have made a mistake in the deduction.

    # Let's go back to the deduction of coffee and tea.

    # clue12: one house between tea and coffee.
    # This means that the positions of tea and coffee differ by 2.

    # So possible pairs: (1,3), (2,4), (3,5), (3,1), etc.

    # Now, coffee cannot be in house2 because house2 has blends and not blue master (clue11).
    # Coffee cannot be in house3 because house3 has root beer.
    # Coffee cannot be in house5 because then tea would need to be in house3, which has root beer.

    # So coffee must be in house1 or house4.

    # If coffee in house1, then tea must be in house3 (|1-3|=2) -> but house3 has root beer -> invalid.
    # If coffee in house4, then tea must be in house2 (|4-2|=2) -> valid.

    # Therefore, coffee must be in house4, and tea in house2.

    # So house4: drink=coffee, and since clue11, house4: cigar=blue master.
    # house2: drink=tea.

    # Then, since house2 has drink=tea, and house2 has cigar=blends (from clue7 and clue8).

    # Now, drinks: house3 has root beer, house4 has coffee, house2 has tea.
    # Left: milk and water for house0 and house1.
    # clue10: milk not in house5 -> so milk must be in house0 or house1 or house2 or house3 or house4, but house2 has tea, house3 has root beer, house4 has coffee, so milk in house0 or house1.
    # So house0 and house1: milk and water.

    # Cigars: house2: blends, house3: pall mall, house4: blue master.
    # Left: dunhill and prince for house0 and house1.

    # Birthdays: house0: april, house1: feb, house2: jan, so house3 and house4 have mar and sept.
    # clue4: dunhill smoker has march birthday.
    # march birthday is in house3 or house4.
    # If march in house3, then house3 must have dunhill, but house3 has pall mall -> invalid.
    # Therefore, march must be in house4, and house4 must have dunhill? but house4 has blue master -> invalid.

    # This is the contradiction.

    # So where is the error?

    # The error is in the assignment of the jan birthday to house3 from clue6.
    # clue6: "There is one house between the person whose birthday is in January and Peter."
    # Peter is in house5 (index4). So the jan birthday could be in house3 (index2) because between house3 and house5 is house4.
    # But it could also be in house2 (index1) because |2-4|=2? wait, |1-4|=3 -> between house2 and house5 there are two houses (3 and 4), so not one house between.
    # Or in house1 (index0): |0-4|=4 -> three houses between.
    # So only house3 (index2) is possible.

    # So then why do we have a contradiction?

    # Perhaps the name assignment is wrong.

    # Let's try to place Bob in house4 instead of house0.

    # We have names: house3: Eric, house4: Arnold, house5: Peter.
    # Then house0 and house1 and house2: Alice, Bob, and one more? wait, we have five names: Peter, Alice, Eric, Bob, Arnold.
    # So house0, house1, house2 must be Alice and Bob and one more? But we have only three houses and two names left? No, we have three houses (0,1,2) and three names: Alice, Bob, and the remaining one? But we have already used Eric, Arnold, Peter. So left Alice and Bob for house0 and house1 and house2? But that's three houses and two names. This means we must have Bob in house2.

    # But then Bob would be in house2, which has feb birthday, but Bob has april birthday -> contradiction.

    # Therefore, the only logical conclusion is that the initial assignment of Arnold and Peter to house4 and house5 is correct, and Bob must be in house0 with april birthday, and Alice in house1 with feb birthday, and then house2 with Eric and jan birthday.

    # Then the error must be in the coffee and tea assignment.

    # Let's list the houses:
    #   house0: Bob, april, ?, ?
    #   house1: Alice, feb, blends, ?
    #   house2: Eric, jan, pall mall, root beer
    #   house3: Arnold, ?, ?, ?
    #   house4: Peter, ?, ?, ?

    # clue4: dunhill has march birthday.
    # clue7: blends has feb birthday -> already satisfied (house1).
    # clue11: blue master is coffee.
    # clue12: one house between tea and coffee.

    # Now, coffee can be in house0, house1, house3, house4 ( since house2 has root beer).
    # But house1 has cigar blends, so if coffee is in house1, then it would require blue master, but it has blends -> cannot. So coffee not in house1.
    # So coffee in house0, house3, or house4.

    # If coffee in house0, then tea must be in house2 (|0-2|=2) -> but house2 has root beer -> invalid.
    # If coffee in house3, then tea must be in house1 (|3-1|=2) or house5 (|3-5|=2) -> house5 is house4? wait, house4 is index4.
    #   So tea in house1 or house5.
    #   If tea in house1, then house1 drink=tea.
    #   Then drinks: house0: ? ( not coffee because coffee in house3), house1: tea, house2: root beer, house3: coffee, house4: ?.
    #   The remaining drinks: milk and water.
    #   clue10: milk not in house5 -> so milk in house0 or house1 or house2 or house3, but house1 has tea, house2 has root beer, house3 has coffee, so milk in house0.
    #   Then house4: water.
    #   Now, cigars: house1: blends, house2: pall mall.
    #   clue11: blue master is coffee -> so house3: blue master.
    #   Remaining cigars: dunhill and prince for house0 and house4.
    #   Birthdays: house0: april, house1: feb, house2: jan, so house3 and house4 have mar and sept.
    #   clue4: dunhill has march birthday.
    #   If march in house3, then house3 must have dunhill, but house3 has blue master -> invalid.
    #   If march in house4, then house4 must have dunhill.
    #   Then house0: prince.
    #   So house3: birthday=sept, cigar=blue master, drink=coffee
    #   house4: birthday=mar, cigar=dunhill, drink=water
    #   house0: drink=milk, cigar=prince
    #   house1: drink=tea
    #   This seems valid.

    #   And clue12: one house between coffee (house3) and tea (house1): |3-1|=2 -> one house between ( house2) -> satisfied.

    # If coffee in house4, then tea must be in house2 (|4-2|=2) -> but house2 has root beer -> invalid.

    # Therefore, the only possibility is coffee in house3.

    # So the solution is:

    # house0: Bob, april, prince, milk
    # house1: Alice, feb, blends, tea
    # house2: Eric, jan, pall mall, root beer
    # house3: Arnold, sept, blue master, coffee
    # house4: Peter, mar, dunhill, water

    # Let's verify all clues:

    # 1. root beer lover is Eric -> house2 -> yes.
    # 2. Pall Mall in third house -> house2 is third house? wait, house2 is index2, which is third house -> yes.
    # 3. April birthday is Bob -> house0 -> yes.
    # 4. Dunhill smoker is march birthday -> house4 has dunhill and mar -> yes.
    # 5. Peter is right of root beer lover: root beer in house2, Peter in house4 -> right -> yes.
    # 6. One house between jan birthday and Peter: jan in house2, Peter in house4 -> between them is house3 -> yes.
    # 7. Blends smoker is feb birthday -> house1 has blends and feb -> yes.
    # 8. Feb birthday in second house -> house1 -> yes.
    # 9. Arnold directly left of Peter: Arnold in house3, Peter in house4 -> yes.
    #10. Milk not in fifth house -> milk in house0 -> yes.
    #11. Blue Master is coffee drinker -> house3 has blue master and coffee -> yes.
    #12. One house between tea and coffee: tea in house1, coffee in house3 -> between them is house2 -> yes.
    #13. Eric in third house -> house2 -> yes.

    # So this is the correct solution.

    # Therefore, we assign accordingly.

    names = ['Bob', 'Alice', 'Eric', 'Arnold', 'Peter']
    birthdays = ['april', 'feb', 'jan', 'sept', 'mar']
    cigars = ['prince', 'blends', 'pall mall', 'blue master', 'dunhill']
    drinks = ['milk', 'tea', 'root beer', 'coffee', 'water']

    # Create the solution dictionary
    solution = {
        "header": ["House", "Name", "Birthday", "Cigar", "Drink"],
        "rows": []
    }

    for i in range(5):
        solution["rows"].append([
            str(i+1),
            names[i],
            birthdays[i],
            cigars[i],
            drinks[i]
        ])

    # Output the solution as JSON
    print(json.dumps({"solution": solution}))

if __name__ == '__main__':
    main()