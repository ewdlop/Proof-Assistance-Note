from enum import Enum
from dataclasses import dataclass
from typing import List, Tuple, Optional

class Term:
    """Represents a term in categorical logic"""
    def __init__(self, name: str):
        self.name = name
    
    def __str__(self) -> str:
        return self.name

class PropositionType(Enum):
    """Four types of categorical propositions"""
    UNIVERSAL_AFFIRMATIVE = "A"  # All S are P
    UNIVERSAL_NEGATIVE = "E"     # No S are P
    PARTICULAR_AFFIRMATIVE = "I" # Some S are P
    PARTICULAR_NEGATIVE = "O"    # Some S are not P

@dataclass
class Proposition:
    """Categorical proposition"""
    type: PropositionType
    subject: Term
    predicate: Term
    
    def __str__(self) -> str:
        if self.type == PropositionType.UNIVERSAL_AFFIRMATIVE:
            return f"All {self.subject} are {self.predicate}"
        elif self.type == PropositionType.UNIVERSAL_NEGATIVE:
            return f"No {self.subject} are {self.predicate}"
        elif self.type == PropositionType.PARTICULAR_AFFIRMATIVE:
            return f"Some {self.subject} are {self.predicate}"
        else:
            return f"Some {self.subject} are not {self.predicate}"
    
    def distribute_subject(self) -> bool:
        """Check if subject is distributed"""
        return self.type in [PropositionType.UNIVERSAL_AFFIRMATIVE, 
                           PropositionType.UNIVERSAL_NEGATIVE]
    
    def distribute_predicate(self) -> bool:
        """Check if predicate is distributed"""
        return self.type in [PropositionType.UNIVERSAL_NEGATIVE]

class Figure(Enum):
    """Four figures of categorical syllogism"""
    FIRST = 1   # M-P, S-M ∴ S-P
    SECOND = 2  # P-M, S-M ∴ S-P
    THIRD = 3   # M-P, M-S ∴ S-P
    FOURTH = 4  # P-M, M-S ∴ S-P

@dataclass
class Syllogism:
    """Categorical syllogism with two premises and conclusion"""
    major_premise: Proposition
    minor_premise: Proposition
    conclusion: Proposition
    
    def get_figure(self) -> Figure:
        """Determine syllogism figure"""
        # Get middle term
        terms = self.get_terms()
        middle = terms['M']
        
        # Check position of middle term
        if (self.major_premise.subject == middle and 
            self.minor_premise.subject == middle):
            return Figure.THIRD
        elif (self.major_premise.predicate == middle and 
              self.minor_premise.predicate == middle):
            return Figure.SECOND
        elif (self.major_premise.subject == middle and 
              self.minor_premise.predicate == middle):
            return Figure.FIRST
        else:
            return Figure.FOURTH
    
    def get_terms(self) -> dict:
        """Get major, minor, and middle terms"""
        # P is major term (predicate of conclusion)
        # S is minor term (subject of conclusion)
        # M is middle term (appears in premises but not conclusion)
        terms = {
            'P': self.conclusion.predicate,
            'S': self.conclusion.subject
        }
        
        # Find middle term (appears in both premises but not conclusion)
        major_terms = {self.major_premise.subject, self.major_premise.predicate}
        minor_terms = {self.minor_premise.subject, self.minor_premise.predicate}
        middle = list(major_terms & minor_terms)[0]
        terms['M'] = middle
        
        return terms
    
    def is_valid(self) -> Tuple[bool, Optional[str]]:
        """
        Check if syllogism is valid
        Returns (valid, reason if invalid)
        """
        # Rule 1: Exactly three terms
        terms = set()
        terms.update([self.major_premise.subject, self.major_premise.predicate])
        terms.update([self.minor_premise.subject, self.minor_premise.predicate])
        terms.update([self.conclusion.subject, self.conclusion.predicate])
        if len(terms) != 3:
            return False, "Must have exactly three terms"
        
        # Rule 2: Middle term must be distributed at least once
        middle = self.get_terms()['M']
        middle_distributed = False
        for premise in [self.major_premise, self.minor_premise]:
            if premise.subject == middle and premise.distribute_subject():
                middle_distributed = True
            if premise.predicate == middle and premise.distribute_predicate():
                middle_distributed = True
        if not middle_distributed:
            return False, "Middle term must be distributed at least once"
        
        # Rule 3: Terms distributed in conclusion must be distributed in premises
        conclusion_subjects = []
        conclusion_predicates = []
        if self.conclusion.distribute_subject():
            conclusion_subjects.append(self.conclusion.subject)
        if self.conclusion.distribute_predicate():
            conclusion_predicates.append(self.conclusion.predicate)
            
        for term in conclusion_subjects:
            distributed = False
            for premise in [self.major_premise, self.minor_premise]:
                if premise.subject == term and premise.distribute_subject():
                    distributed = True
                if premise.predicate == term and premise.distribute_predicate():
                    distributed = True
            if not distributed:
                return False, f"Term {term} is distributed in conclusion but not in premises"
        
        # Rule 4: Cannot have two negative premises
        if (self.major_premise.type in [PropositionType.UNIVERSAL_NEGATIVE, 
                                      PropositionType.PARTICULAR_NEGATIVE] and
            self.minor_premise.type in [PropositionType.UNIVERSAL_NEGATIVE, 
                                      PropositionType.PARTICULAR_NEGATIVE]):
            return False, "Cannot have two negative premises"
        
        # Rule 5: If one premise is negative, conclusion must be negative
        if (self.major_premise.type in [PropositionType.UNIVERSAL_NEGATIVE, 
                                      PropositionType.PARTICULAR_NEGATIVE] or
            self.minor_premise.type in [PropositionType.UNIVERSAL_NEGATIVE, 
                                      PropositionType.PARTICULAR_NEGATIVE]):
            if self.conclusion.type not in [PropositionType.UNIVERSAL_NEGATIVE, 
                                          PropositionType.PARTICULAR_NEGATIVE]:
                return False, "If premise is negative, conclusion must be negative"
        
        # Rule 6: Cannot have two particular premises
        if (self.major_premise.type in [PropositionType.PARTICULAR_AFFIRMATIVE, 
                                      PropositionType.PARTICULAR_NEGATIVE] and
            self.minor_premise.type in [PropositionType.PARTICULAR_AFFIRMATIVE, 
                                      PropositionType.PARTICULAR_NEGATIVE]):
            return False, "Cannot have two particular premises"
        
        return True, None

def example_usage():
    """Demonstrate categorical syllogism analysis"""
    
    # Example 1: Valid syllogism in first figure (Barbara)
    # All M are P
    # All S are M
    # Therefore, all S are P
    major = Proposition(PropositionType.UNIVERSAL_AFFIRMATIVE, 
                       Term("M"), Term("P"))
    minor = Proposition(PropositionType.UNIVERSAL_AFFIRMATIVE, 
                       Term("S"), Term("M"))
    conclusion = Proposition(PropositionType.UNIVERSAL_AFFIRMATIVE, 
                           Term("S"), Term("P"))
    
    syllogism = Syllogism(major, minor, conclusion)
    valid, reason = syllogism.is_valid()
    
    print("Syllogism 1:")
    print(f"Major premise: {major}")
    print(f"Minor premise: {minor}")
    print(f"Conclusion: {conclusion}")
    print(f"Figure: {syllogism.get_figure()}")
    print(f"Valid: {valid}")
    if not valid:
        print(f"Reason: {reason}")
    
    # Example 2: Invalid syllogism (undistributed middle)
    # All P are M
    # All S are M
    # Therefore, all S are P
    major = Proposition(PropositionType.UNIVERSAL_AFFIRMATIVE, 
                       Term("P"), Term("M"))
    minor = Proposition(PropositionType.UNIVERSAL_AFFIRMATIVE, 
                       Term("S"), Term("M"))
    conclusion = Proposition(PropositionType.UNIVERSAL_AFFIRMATIVE, 
                           Term("S"), Term("P"))
    
    syllogism = Syllogism(major, minor, conclusion)
    valid, reason = syllogism.is_valid()
    
    print("\nSyllogism 2:")
    print(f"Major premise: {major}")
    print(f"Minor premise: {minor}")
    print(f"Conclusion: {conclusion}")
    print(f"Figure: {syllogism.get_figure()}")
    print(f"Valid: {valid}")
    if not valid:
        print(f"Reason: {reason}")

if __name__ == "__main__":
    example_usage()
